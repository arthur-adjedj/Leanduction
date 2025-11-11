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

-- def Level.mkNaryIMax : List Level → Level
  -- | []    => levelZero
  -- | [u]   => u
  -- | u::us => mkLevelIMax' u (mkNaryIMax us)

namespace SparseParametricityTranslation

structure Context where
  paramsFVars : Array Expr
  predsFVars : Array (Option Expr)
  sparseIndNames : Array Name
  sparseIndFVars : Array Expr
  sparseIndTypes : Array Expr
deriving Inhabited

instance : ToMessageData Context where
  toMessageData ctx := m!"paramsFVars: {ctx.paramsFVars}\npredsFVars: {ctx.predsFVars}\nsparseIndNames: {ctx.sparseIndNames}\nsparseIndFVars: {ctx.sparseIndFVars}\nsparseIndTypes: {ctx.sparseIndTypes}"

abbrev M := ReaderT Context MetaM

def withSparseParamIndType [Inhabited α] (info : InductiveVal) (positivityMask : Array Bool) (sparseIndNames : Array Name) /-(predUnivs : Array (Option Name))-/ (k : M α): MetaM α := do
  forallBoundedTelescope info.type info.numParams fun paramsFVars _ => do
    withPredicates paramsFVars 0 #[] fun predsFVars => do
      let indNames := info.all
      let indTypes ← indNames.mapM (fun name => inferType (mkConst name (info.levelParams.map Level.param)))
      let sparseIndTypes ← indTypes.toArray.mapM fun indTy => forallBoundedTelescope indTy info.numParams fun oldParamFVars ty => do
        let ty := ty.replaceFVars oldParamFVars paramsFVars
        forallTelescopeReducing ty fun indices _s => do
          -- let .sort u := s | unreachable!
          -- let predsMaxes : Level := Level.mkNaryIMax ((predUnivs.filterMap id).toList.map Level.param)
          let indTy := (mkAppN (mkConst info.name (info.levelParams.map Level.param)) (paramsFVars ++ indices))
          let ty ← mkArrow indTy (.sort 0 /- (mkLevelIMax' predsMaxes u)-/ )
          let ty ← mkForallFVars indices ty
          let ty ← mkForallFVars (predsFVars.filterMap id) ty
          mkForallFVars paramsFVars ty
      withLocalDeclsDND (sparseIndNames.zip sparseIndTypes) fun sparseIndFVars =>
        k.run {paramsFVars, predsFVars, sparseIndNames, sparseIndFVars, sparseIndTypes}
where
  withPredicates (fvars : Array Expr) (i : Nat) (preds : Array (Option Expr)) (k : Array (Option Expr) → MetaM α): MetaM α := do
    if i < fvars.size then
      if positivityMask[i]! then
        let ty ← inferType fvars[i]!
        let predTy ← forallTelescopeReducing ty fun llargs _ => do
          let predTy ← mkArrow (mkAppN fvars[i]! llargs) (mkSort 0 /-(.param predUnivs[i]!.get!)-/)
          mkForallFVars llargs predTy
        logInfo m!"predTy : {predTy}"
        withLocalDecl `P .default predTy fun pred =>
          withPredicates fvars (i+1) (preds.push pred) k
      else
        withPredicates fvars (i+1) (preds.push none) k
    else
      k preds

partial def sparseParamConstrType
  (info : InductiveVal)
  (indIdx : Nat)
  (ctor : ConstructorVal) (ctx : Context): MetaM Expr := do
  -- c : As -> args -> I As Ds
  forallBoundedTelescope ctor.type info.numParams fun params ty => do
    let ty := ty.replaceFVars params ctx.paramsFVars
    -- ty := args -> I As Ds
    forallTelescope ty fun args indAsDs => do
      -- ty := I As Ds
      withConstPreds ctx.paramsFVars args 0 #[] fun constPreds => do
        -- indices := Ds
        let indices := Expr.getAppArgsN indAsDs info.numIndices
        -- ty := IP As
        let ty := mkAppN ctx.sparseIndFVars[indIdx]! ctx.paramsFVars
        -- ty := IP As PAs
        let ty := mkAppN ty (ctx.predsFVars.filterMap id)
        -- ty := IP As PAs Ds
        let ty := mkAppN ty indices
        -- ty := IP As PAs Ds (c As args)
        let cAs := mkAppN (mkConst ctor.name (info.levelParams.map Level.param)) ctx.paramsFVars
        let cAsArgs := mkAppN cAs args
        let ty := mkApp ty cAsArgs
        -- ty := PArgs -> IP As PAs
        let ty ← mkForallFVars (constPreds.filterMap id) ty
        -- ty := Args -> PArgs -> IP As PAs
        let ty ← mkForallFVars args ty
        -- ty := PAs -> Args -> PArgs -> IP As PAs
        let ty ← mkForallFVars (ctx.predsFVars.filterMap id) ty
        -- ty := As -> PAs -> Args -> PArgs -> IP As PAs
        let ty ← mkForallFVars ctx.paramsFVars ty
        logInfo m!"sparseParamConstrType {ctor.name} = {ty}"
        return ty
where
  -- TODO remove MetaM monad once logInfo removed
  getParamPred? (params : Array Expr) (f : FVarId) : Option Expr := Id.run do
    if let some idx := params.findIdx? (·.fvarId! == f) then
      return ctx.predsFVars[idx]!
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
                let ty := mkAppN ctx.sparseIndFVars[idx]! fnargs[0...params.size]
                logInfo m!"step 1: {ty}"
                let ty := mkAppN ty (ctx.predsFVars.filterMap id)
                logInfo m!"step 2: {ty}"
                let ty := mkApp ty (mkAppN arg conArgArgs)
                logInfo m!"step 3: {ty}"
                let ty ← mkForallFVars conArgArgs ty
                logInfo m!"step 4: {ty}"
                return ty
              else
                let fnLvls := fn'.constLevels!
                let nestedInd ← getConstInfoInduct fn
                let nestedIndSparseName := fn ++ `Sparse
                unless ← isInductive nestedIndSparseName do
                  throwError "Failed to generate Sparse translation of {info.all[indIdx]!}: Sparse translation for nested type {fn} does not exist"
                let nestedParamsMask ← NestedPositivity.positiveParams nestedInd
                let nestedIndParams := fnargs[0...nestedInd.numParams]
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
                logInfo m!"PAs : {PAs}"
                -- let PAsUnivs : Array (Option Level) ← PAs.mapM (fun | none => pure none | some e => do forallTelescopeReducing (← inferType e) fun _ s => pure s.sortLevel!)
                -- let PAsUnivs := PAsUnivs.filterMap id |>.toList
                -- Is As
                let ty := mkAppN (mkConst nestedIndSparseName fnLvls /-(PAsUnivs ++ fnLvls)-/) nestedIndParams
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

def checkConstant (name : Name): MetaM Unit := do
  let env ← getEnv
  if env.find? name |>.isSome then
    throwError "Failed to add sparse translation, {name} already exists"

-- def mkAuxConstructions (declNames : Array Name) : TermElabM Unit := do
  -- for n in declNames do
    -- mkRecOn n
    -- mkCasesOn n
    -- mkCtorIdx n
    -- mkCtorElim n
    -- mkNoConfusion n
    -- mkBelow n
  -- for n in declNames do
    -- mkBRecOn n
  -- mkSizeOfInstances declNames[0]!
  -- for n in declNames do
    -- mkInjectiveTheorems n

-- def withPredUnivs (positiveParams : Array Bool) (k : Array (Option Name) → TermElabM α): TermElabM α := do
  -- let univName := `p
  -- let mut idx := 1
  -- let mut levelNames := Array.replicate positiveParams.size none
  -- for i in 0...positiveParams.size do
    -- if positiveParams[i]! then
      -- let univName := univName.appendIndexAfter idx
      -- idx := idx+1
      -- levelNames := levelNames.modify i (fun _ => some univName)
  -- Term.withLevelNames (levelNames.filterMap id).toList (k levelNames)

def addSparseTranslation (indName : Name) : TermElabM Unit :=
  withOptions (fun opt => opt.set `genSizeOf false) do
  let indVal ← getConstInfoInduct indName
  let sparseIndNames := indVal.all.toArray.map (fun n => n ++ `Sparse)
  sparseIndNames.forM (checkConstant ·)
  Term.withLevelNames indVal.levelParams do
    let positivityMask ← NestedPositivity.positiveParams indVal
    -- withPredUnivs positivityMask fun _predUnivs => do
    let sparseIndUnivs := /-(predUnivs.filterMap id).toList ++-/ indVal.levelParams
    withSparseParamIndType indVal positivityMask sparseIndNames /-predUnivs-/ $ do
      logInfo m!"Ctx: {← read}"
      let mut sparseInds := []
      let sparseIndsWithAsPAs ← do
        -- let preds := (← read).predsFVars.filterMap id
        -- let AsPas := (← read).paramsFVars ++ preds
        (← read).sparseIndNames.mapM fun name  =>
          return mkConst name (sparseIndUnivs.map Level.param)
          -- return mkAppN PId AsPas
      logInfo m!"sparseIndsWithAsPAs : {sparseIndsWithAsPAs}"
      for (indName,indIdx) in indVal.all.zipIdx do
        let indVal ← getConstInfoInduct indName
        let sparseInd : InductiveType ← do
          pure {
            name := (← read).sparseIndNames[indIdx]!
            type  := (← read).sparseIndTypes[indIdx]!
            ctors := ← sparseConstructors indVal indIdx sparseIndsWithAsPAs indVal.ctors
          }
        sparseInds := sparseInd::sparseInds
      let numParams := indVal.numParams + positivityMask.foldl (init := 0) (fun acc b => if b then acc+1 else acc)
      addDecl (.inductDecl sparseIndUnivs numParams sparseInds false)
      -- mkAuxConstructions (sparseInds.map (·.name) |>.toArray)
where
  sparseConstructors (indVal : InductiveVal) (indIdx : Nat) (sparseIndsWithAsPAs : Array Expr ) (ctors : List Name) : M (List Constructor) :=
    match ctors with
      | [] => return []
      | ctorName::tl => do
        let name := ctorName.replacePrefix indVal.name (indVal.name ++ `Sparse)
        checkConstant name
        let ctor ← getConstInfoCtor ctorName
        let type ← sparseParamConstrType indVal indIdx ctor
        let type := type.replaceFVars (← read).sparseIndFVars sparseIndsWithAsPAs
        logInfo m!"ctor: {name} : {type}"
        return {name, type}::(← sparseConstructors indVal indIdx sparseIndsWithAsPAs tl)

end SparseParametricityTranslation
