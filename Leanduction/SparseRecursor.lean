import Lean
import Leanduction.NestedPositivity
import Leanduction.SparseParametricity

open Lean Elab Meta

namespace SparseRecursor

partial def replaceNestedMotives (indVals : List InductiveVal) (realMotives : Array Expr) (nestedMotives : Array Expr) : MetaM (Array Expr) := do
  go 0 #[]
where
  go (i : Nat) (acc : Array Expr) : MetaM (Array Expr) :=
    if _ : i < nestedMotives.size then do
      -- Ds -> Is As Ds -> Prop
      let nestedMotive : Expr ← forallTelescope (← inferType nestedMotives[i]) fun xs ty => do
        let major := xs[xs.size-1]!
        let majorType ← inferType major
        let ty ← nestedMotive majorType
        let ty := mkApp ty major
        mkLambdaFVars xs ty
      logInfo m!"nestedMotive : {nestedMotive}"
      go (i+1) (acc.push nestedMotive)
    else
      return acc

  nestedMotive (motiveType : Expr) : MetaM Expr := do
    logInfo m!"nestedMotive {motiveType}"
    motiveType.withApp fun fn args =>  do
      let nestedIndName := fn.constName!
      let nestedIndVal ← getConstInfoInduct nestedIndName
      let nestedParams := args[0...nestedIndVal.numParams].toArray
      let nestedParamsMask ← NestedPositivity.positiveParams nestedIndVal
      let sparseNestedIndName := SparseParametricityTranslation.sparseName fn.constName!
      let ty := mkAppN (mkConst sparseNestedIndName fn.constLevels!) nestedParams
      logInfo m!"step 1 : {ty}"
      let preds ← nestedParams.mapIdxM fun idx e => if nestedParamsMask[idx]! then return some ( ← genPred e) else pure none
      logInfo m!"preds : {preds}"
      let ty := mkAppN ty (preds.filterMap id)
      logInfo m!"step 2 : {ty}"
      let ty := mkAppN ty args[nestedIndVal.numParams...*]
      logInfo m!"step 3 : {ty}"
      logInfo m!"step 4 : {ty}"
      logInfo m!"step 5 : {ty}"
      return ty

  genPred (param : Expr) : MetaM Expr := do
    logInfo m!"genPred {param}"
    forallTelescope param fun xs ty => do
      let fallback := mkLambdaFVars xs (mkConst `True)
      if !(param.getUsedConstants.any indVals[0]!.all.contains) then
        return (← fallback)
      ty.withApp fun fn args => do
        let fnName := fn.constName!
        if let some indIdx := indVals[0]!.all.findIdx? (· == fnName) then
          let ty := realMotives[indIdx]!
          let ty := mkAppN ty args[indVals[indIdx]!.numIndices...*]
          let ty := ty
          withLocalDeclD `f param fun f => do
            let ty := mkApp ty (mkAppN f xs)
            let ty ← mkForallFVars xs ty
            let motive ← mkLambdaFVars #[f] ty
            return motive
        else
          let ty ← nestedMotive ty
          withLocalDeclD `f param fun f => do
            let ty := mkApp ty (mkAppN f xs)
            let ty ← mkForallFVars xs ty
            let motive ← mkLambdaFVars #[f] ty
            return motive

-- TODO generate the term at the same time ?
def type (indName : Name) : MetaM Expr := do
  let info ← getConstInfoInduct indName
  let indVals ← info.all.mapM getConstInfoInduct
  let recInfo ← getConstInfoRec (info.name ++ `rec)
  let recTypeToProp := match recInfo.levelParams with
    | [] => recInfo.type
    | motiveUniv::_ => recInfo.type.instantiateLevelParams [motiveUniv] [0]
  forallTelescope recTypeToProp fun xs ty => do
    let params := xs[0...info.numParams]
    let indices_and_major := xs[recInfo.getFirstIndexIdx...*]
    let motives := xs[info.numParams...info.numParams + info.all.length]
    let nestedMotives := xs[(info.numParams + info.all.length)...recInfo.getFirstMinorIdx]
    let sparseForNestedMotives ←  replaceNestedMotives indVals motives nestedMotives
    logInfo m!"sparseForNestedMotives : {sparseForNestedMotives}"
    let numMinors := indVals.foldl (init := 0) (fun acc ind => acc + ind.ctors.length)
    let oldMinors := xs[recInfo.getFirstMinorIdx...recInfo.getFirstMinorIdx + numMinors]
    let lctx ← getLCtx
    let lctx := oldMinors.foldl (init := lctx) (fun lctx e => lctx.modifyLocalDecl e.fvarId! fun ldecl => ldecl.setType (Expr.replaceFVars ldecl.type nestedMotives sparseForNestedMotives))
    Meta.withLCtx' lctx do
      let minors := oldMinors.toArray.map (Expr.replaceFVars · nestedMotives sparseForNestedMotives)
      let ty ← mkForallFVars indices_and_major ty
      let ty ← mkForallFVars minors ty
      let ty ← mkForallFVars motives ty
      let ty ← mkForallFVars params ty
      Meta.check ty
      return ty

end SparseRecursor
