import Lean

open Lean Elab Meta

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
          let params := xs[0...numParams]
          for i in 0...numParams do
            unless (← isTypeFormerType (← inferType params[i]!)) do
              maskRef.modify (Array.modify · i fun _ => false)
          for conArg in xs[numParams...*] do
            forallTelescopeReducing (← inferType conArg) fun conArgArgs conArgRes => do
              let badFVars ← IO.mkRef (default : CollectFVars.State)
              for conArgArg in conArgArgs do
                badFVars.modify (Lean.collectFVars · (← inferType conArgArg))
              let conArgRes ← whnf conArgRes
              if conArgRes.hasAnyFVar (fun f => params.any (·.fvarId! == f)) then
                  conArgRes.withApp fun fn args => do
                    if let some p := fn.fvarId? then
                      for arg in args do
                        if arg.hasAnyFVar (· == p) then
                          badFVars.modify (Lean.CollectFVars.State.add · p)
                    else if let some fn := fn.constName? then
                      if info.all.contains fn then
                        -- Recursive occurrence of an inductive type of this group.
                        -- Params must match by construction but check indices
                        for idxArg in args[info.numParams...*] do
                          badFVars.modify (Lean.collectFVars · idxArg)
                      else if (← isInductive fn) then
                        let info' ← getConstInfoInduct fn
                        let indMask ← positiveParams info'
                        for i in 0...info'.numParams do
                          if !indMask[i]! then
                            badFVars.modify (Lean.collectFVars · args[i]!)
                      else
                        for arg in args do
                          badFVars.modify (Lean.collectFVars · arg)
                    else
                      badFVars.modify (Lean.collectFVars · conArgRes)

              let badFVars : Std.TreeSet _ _ := (← badFVars.get).fvarSet
              for i in 0...numParams do
                if params[i]!.fvarId! ∈ badFVars then
                  maskRef.modify (Array.modify · i fun _ => false)
    maskRef.get

end NestedPositivity

namespace SparseParametricityTranslation

def withSparseParamIndType (info : InductiveVal) (positivityMask : Array Bool) (k : Array Expr → Array (Option Expr) → Expr → MetaM α): MetaM α := do
  forallBoundedTelescope info.type info.numParams fun params ty => do
    withPredicates params 0 #[] fun preds => do
      let ty ← forallTelescopeReducing ty fun indices ty => do
        let indTy := (mkAppN (mkConst info.name (info.levelParams.map Level.param)) (params ++ indices))
        let ty ← mkArrow indTy ty
        mkForallFVars indices ty
      let ty ← mkForallFVars (preds.filterMap id) ty
      let ty ← mkForallFVars params ty
      k params preds ty
where
  withPredicates (fvars : Array Expr) (i : Nat) (preds : Array (Option Expr)) (k : Array (Option Expr) → MetaM α): MetaM α := do
    if i < fvars.size then
      if positivityMask[i]! then
        let ty ← inferType fvars[i]!
        let predTy ← forallTelescopeReducing ty fun llargs ty => do
          let predTy ← mkArrow (mkAppN fvars[i]! llargs) ty
          mkForallFVars llargs predTy
        withLocalDecl `P .default predTy fun pred =>
          withPredicates fvars (i+1) (preds.push pred) k
      else
        withPredicates fvars (i+1) (preds.push none) k
    else
      k preds

partial def sparseParamConstrType (info : InductiveVal) (sparseInds : Array Expr) (indIdx : Nat) (oldParams : Array Expr) (preds : Array (Option Expr)) (ctor : ConstructorVal) : MetaM Expr := do
  -- c : As -> args -> I As Ds
  forallBoundedTelescope ctor.type info.numParams fun params ty =>
    let ty := ty.replaceFVars params oldParams
    -- ty := args -> I As Ds
    forallTelescope ty fun args indAsDs =>
      -- ty := I As Ds
      withConstPreds oldParams args 0 #[] fun constPreds => do
        -- indices := Ds
        let indices := Expr.getAppArgsN indAsDs info.numIndices
        -- ty := IP As
        let ty := mkAppN sparseInds[indIdx]! oldParams
        -- ty := IP As PAs
        let ty := mkAppN ty (preds.filterMap id)
        -- ty := IP As PAs Ds
        let ty := mkAppN ty indices
        -- ty := IP As PAs Ds (c As args)
        let cAs := mkAppN (mkConst ctor.name (info.levelParams.map Level.param)) oldParams
        let cAsArgs := mkAppN cAs args
        let ty := mkApp ty cAsArgs
        -- ty := PArgs -> IP As PAs
        let ty ← mkForallFVars (constPreds.filterMap id) ty
        -- ty := Args -> PArgs -> IP As PAs
        let ty ← mkForallFVars args ty
        -- ty := PAs -> Args -> PArgs -> IP As PAs
        let ty ← mkForallFVars (preds.filterMap id) ty
        -- ty := As -> PAs -> Args -> PArgs -> IP As PAs
        let ty ← mkForallFVars oldParams ty
        logInfo m!"sparseParamConstrType {ctor.name} = {ty}"
        return ty
where
  -- TODO remove MetaM monad once logInfo removed
  getParamPred? (params : Array Expr) (f : FVarId) : Option Expr := Id.run do
    if let some idx := params.findIdx? (·.fvarId! == f) then
      return preds[idx]!
    else
      none

  withConstPreds (params args : Array Expr) (argIdx : Nat) (constPreds : Array (Option Expr)) (k : Array (Option Expr) → MetaM Expr) : MetaM Expr := do
    if argIdx < args.size then
      let arg := args[argIdx]!
      if let some ty ← predOfArg params arg then
        withLocalDecl `P .default ty fun constPred =>
          withConstPreds params args (argIdx+1) (constPreds.push constPred) k
      else withConstPreds params args (argIdx+1) (constPreds.push none) k
    else
      k constPreds

  predOfArg (params : Array Expr) (arg: Expr) : MetaM (Option Expr) := do
    let argTy ← inferType arg
    let argTy ← whnf argTy
    forallTelescope argTy fun conArgArgs conArgRes => do
        if conArgRes.hasAnyFVar (fun f => getParamPred? params f |>.isSome) then
          conArgRes.withApp fun fn' fnargs => do
            if let some p := fn'.fvarId? then
              if let some predFVar := getParamPred? params p then
                let ty := mkAppN predFVar fnargs
                let ty := mkApp ty (mkAppN arg conArgArgs)
                let ty ← mkForallFVars conArgArgs ty
                return ty
              else
                return none
            else if let some fn := fn'.constName? then
              if (← isInductive fn) then
                if let some idx := info.all.findIdx? (· == fn) then
                  let ty := mkAppN sparseInds[idx]! fnargs
                  let ty := mkApp ty conArgRes
                  let ty ← mkForallFVars conArgArgs ty
                  return ty
                else
                  let fnLvls := fn'.constLevels!
                  let nestedInd ← getConstInfoInduct fn
                  let nestedIndSparseName := fn ++ `Sparse
                  unless ← isInductive nestedIndSparseName do
                    throwError "Failed to generate Sparse translation of {info.all[indIdx]!}: Sparse translation for nested type {fn} does not exist"
                  let nestedParamsMask ← NestedPositivity.positiveParams nestedInd
                  let nestedIndParams := fnargs[0...nestedInd.numParams]
                  -- Is As
                  let ty := mkAppN (mkConst nestedIndSparseName fnLvls) nestedIndParams
                  let PAs ← nestedIndParams.toArray.zipIdx.mapM fun (nestedArgarg,idx) =>
                    if nestedParamsMask[idx]! then
                      forallTelescope nestedArgarg fun xs ty => do
                        withLocalDeclD `z (← mkForallFVars xs ty) fun arg => do
                          let pred ← do
                            if let some P ← predOfArg params arg then
                              pure P
                            else
                              let .sort u ← inferType ty | unreachable!
                              pure (mkConst ``PUnit [u])
                          let P ← mkLambdaFVars #[arg] pred
                          return some P
                    else return none
                  -- Is As PAs
                  let ty := mkAppN ty (PAs.filterMap id)
                  -- Is As PAs Ds
                  let ty := mkAppN ty fnargs[0...nestedInd.numIndices]
                  -- llargs -> Is As PAs Ds
                  let ty := mkApp ty (mkAppN arg conArgArgs)
                  -- llargs -> Is As PAs Ds
                  let ty ← mkForallFVars conArgArgs ty
                  return ty
              else return none
            else return none
        else return none



def addSparseTranslation (indName : Name) : TermElabM Unit := do
  let indVal ← getConstInfoInduct indName
  let sparseIndNames := indVal.all.toArray.map (fun n => n ++ `Sparse)
  Term.withLevelNames indVal.levelParams do
    let levelParams := indVal.levelParams.map Level.param
    let sparseIndTypes := sparseIndNames.map (mkConst · levelParams)
    let positivityMask ← NestedPositivity.positiveParams indVal
    let mut sparseInds := []
    for (indName,indIdx) in indVal.all.zipIdx do
      let indVal ← getConstInfoInduct indName
      let sparseInd : InductiveType ←  withSparseParamIndType indVal positivityMask fun params preds ty => do
        logInfo m!"SparseType : {ty}"
        return {
          name := indName ++ `Sparse
          type  := ty
          ctors := ← sparseConstructors indVal indIdx params preds sparseIndTypes indVal.ctors
        }
      sparseInds := sparseInd::sparseInds
    let numParams := indVal.numParams + positivityMask.foldl (init := 0) (fun acc b => if b then acc+1 else acc)
    addDecl (.inductDecl indVal.levelParams numParams sparseInds false)
where
  sparseConstructors (indVal : InductiveVal) (indIdx : Nat) (params : Array Expr) (preds : Array (Option Expr)) (sparseIndTypes : Array Expr) (ctors : List Name) : MetaM (List Constructor) :=
    match ctors with
      | [] => return []
      | ctor::tl => do
        let name := ctor ++ `Sparse
        let ctor ← getConstInfoCtor ctor
        let type ← sparseParamConstrType indVal sparseIndTypes indIdx params preds ctor
        logInfo m!"{name} : {type}"
        return {name, type}::(← sparseConstructors indVal indIdx params preds sparseIndTypes tl)

end SparseParametricityTranslation
