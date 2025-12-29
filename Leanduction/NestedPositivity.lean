import Lean

open Lean Elab Meta

/-Adapted from `https://github.com/leanprover/lean4/pull/9895`-/
namespace NestedPositivity

structure PositivityExtState where
  map : PHashMap Name (Array Bool) := {}
  deriving Inhabited

/- Simple local extension for caching/memoization -/
initialize positivityExt : EnvExtension PositivityExtState ←
  -- Using `local` allows us to use the extension in `realizeConst` without specifying `replay?`.
  -- The resulting state can still be accessed on the generated declarations using `findStateAsync`;
  -- see below
  registerEnvExtension (pure {}) (asyncMode := .local)

private def positivityExt.getOrSet (key : Name) (act : CoreM (Array Bool)) := do
  match (positivityExt.getState (asyncMode := .async .asyncEnv) (asyncDecl := key) (← getEnv)).map.find? key with
  | some r =>
    return r
  | none =>
    let r ← act
    modifyEnv fun env =>
      positivityExt.modifyState env (fun s => { s with map := s.map.insert key r })
    return r

/--
Throws an exception unless the `i`th parameter of the inductive type only occurrs in
positive position.
-/
partial def positiveParams (info : InductiveVal) : MetaM (Array Bool) := do
  withTraceNode `Leanduction.NestedPositivity (fun e => return m!"{exceptEmoji e} positiveParams {info.name} = {e.toOption}") do
  -- Consistently use the info of the first inductive in the group
  if info.name != info.all[0]! then
    return (← positiveParams (← getConstInfoInduct info.all[0]!))
  let numParams := info.numParams
  let maskRef ← IO.mkRef (Array.replicate numParams true)

  positivityExt.getOrSet info.name do MetaM.run' do
    for indName in info.all do
      let info ← getConstInfoInduct indName
      for con in info.ctors do
        let con ← getConstInfoCtor con
        forallTelescopeReducing con.type fun xs _t => do
          let params := xs[0:numParams]
          for i in [0:numParams] do
            unless (← isTypeFormerType (← inferType params[i]!)) do
              maskRef.modify (Array.modify · i fun _ => false)
          for conArg in xs[numParams:] do
            forallTelescopeReducing (← inferType conArg) fun conArgArgs conArgRes => do
              let badFVars ← IO.mkRef (default : CollectFVars.State)
              for conArgArg in conArgArgs do
                badFVars.modify (Lean.collectFVars · (← inferType conArgArg))
              let conArgRes ← whnf conArgRes
              if conArgRes.hasAnyFVar (fun f => params.any (·.fvarId! == f)) then
                conArgRes.withApp fun fn args => do
                  if fn.isFVar then
                    for arg in args do
                      badFVars.modify (Lean.collectFVars · arg)
                  else if let some fn := fn.constName? then
                    if info.all.contains fn then
                      -- Recursive occurrence of an inductive type of this group.
                      -- Params must match by construction but check indices
                      for idxArg in args[info.numParams:] do
                        badFVars.modify (Lean.collectFVars · idxArg)
                    else if (← isInductive fn) then
                      let info' ← getConstInfoInduct fn
                      let indMask ← positiveParams info'
                      for i in [0:info'.numParams] do
                        if !indMask[i]! then
                          badFVars.modify (Lean.collectFVars · args[i]!)
                    else
                      for arg in args do
                        badFVars.modify (Lean.collectFVars · arg)
                  else
                    badFVars.modify (Lean.collectFVars · conArgRes)
              let badFVars : Std.TreeSet _ _ := (← badFVars.get).fvarSet
              for i in [0:numParams] do
                if params[i]!.fvarId! ∈ badFVars then
                  maskRef.modify (Array.modify · i fun _ => false)
    maskRef.get

end NestedPositivity

initialize
  registerTraceClass `Leanduction.NestedPositivity (inherited := true)
