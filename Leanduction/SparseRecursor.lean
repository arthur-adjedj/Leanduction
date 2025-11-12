import Lean
import Leanduction.NestedPositivity
import Leanduction.SparseParametricity

open Lean Elab Meta

namespace SparseRecursor

partial def replaceNestedMotivesAndMinors (indVals : List InductiveVal) (realMotives : Array Expr) (nestedMotives : Array Expr) : MetaM (Array Expr × Array Expr) := do
  go 0 #[] #[]
where
  go (i : Nat) (motivesReplacements minorsReplacements : Array Expr): MetaM (Array Expr × Array Expr) :=
    if _ : i < nestedMotives.size then do
      -- Ds -> Is As Ds -> Prop
      let nestedMotiveAndMinors : (Expr × Array Expr) ← forallTelescope (← inferType nestedMotives[i]) fun xs ty => do
        let major := xs[xs.size-1]!
        let majorType ← inferType major
        let (ty,minors) ← nestedMotiveAndMinors majorType false
        let ty := mkApp ty major
        let ty ← mkLambdaFVars xs ty
        return (ty,minors)
      logInfo m!"nestedMotive : {nestedMotiveAndMinors}"
      go (i+1) (motivesReplacements.push nestedMotiveAndMinors.1) (minorsReplacements.append nestedMotiveAndMinors.2)
    else
      return (motivesReplacements,minorsReplacements)

  nestedMotiveAndMinors (motiveType : Expr) (noMinors : Bool) : MetaM (if noMinors then Expr else Expr × Array Expr) := do
    logInfo m!"nestedMotive {motiveType}"
    motiveType.withApp fun fn args =>  do
      let nestedIndName := fn.constName!
      let nestedIndVal ← getConstInfoInduct nestedIndName
      let nestedParams := args[0...nestedIndVal.numParams].toArray
      let nestedParamsMask ← NestedPositivity.positiveParams nestedIndVal
      let sparseNestedIndName := SparseParametricityTranslation.sparseName fn.constName!
      let ty := mkAppN (mkConst sparseNestedIndName fn.constLevels!) nestedParams
      let preds ← nestedParams.mapIdxM fun idx e => if nestedParamsMask[idx]! then return some (← genPred e) else pure none
      let ty := mkAppN ty (preds.filterMap id)
      let ty := mkAppN ty args[nestedIndVal.numParams...*]
      match noMinors with
        | true => return ty
        | false => do
          let sparseNestedIndVal ← getConstInfoInduct sparseNestedIndName
          let minors := sparseNestedIndVal.ctors.toArray.map fun ctorName =>
              mkAppN (mkAppN (mkConst ctorName fn.constLevels!) nestedParams) (preds.filterMap id)
          return (ty,minors)

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
          let ty := mkAppN ty args[indVals[indIdx]!.numParams...*]
          withLocalDeclD `f param fun f => do
            let ty := mkApp ty (mkAppN f xs)
            let ty ← mkForallFVars xs ty
            let motive ← mkLambdaFVars #[f] ty
            return motive
        else
          let ty ← nestedMotiveAndMinors ty true
          withLocalDeclD `f param fun f => do
            let ty := mkApp ty (mkAppN f xs)
            let ty ← mkForallFVars xs ty
            let motive ← mkLambdaFVars #[f] ty
            return motive

def genSparseRec (indName : Name) : TermElabM Unit := do
  let info ← getConstInfoInduct indName
  let indVals ← info.all.mapM getConstInfoInduct
  let recName := info.name ++ `rec
  let recInfo ← getConstInfoRec recName
  let recTypeToProp := match recInfo.levelParams with
    | [] => recInfo.type
    | motiveUniv::_ => recInfo.type.instantiateLevelParams [motiveUniv] [0]
  forallTelescope recTypeToProp fun xs ty => do
    let params := xs[0...info.numParams]
    let indices_and_major := xs[recInfo.getFirstIndexIdx...*]
    let motives := xs[info.numParams...info.numParams + info.all.length]
    let nestedMotives := xs[(info.numParams + info.all.length)...recInfo.getFirstMinorIdx]
    let (sparseForNestedMotives,nestedsMinors) ← replaceNestedMotivesAndMinors indVals motives nestedMotives
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
      let recUnivs := match recInfo.levelParams with
        | [] => []
        | _::us => 0::us.map Level.param
      let te := mkConst recName recUnivs
      let te := mkAppN te params
      let te := mkAppN te motives
      let te := mkAppN te sparseForNestedMotives
      let te := mkAppN te minors
      let te := mkAppN te nestedsMinors
      let te ← mkLambdaFVars minors te
      let te ← mkLambdaFVars motives te
      let te ← mkLambdaFVars params te
      logInfo m!"term : {te}"
      Meta.check te
      addDecl <| .defnDecl {
        name := indName ++ `rec_sparse
        levelParams := match recInfo.levelParams with | [] => [] | _::tl => tl
        type := ty
        value := te
        hints := .regular 0 --TODO figure out how important that is ?
        safety := .safe
        }
      Term.applyAttributes (indName ++ `rec_sparse) #[{name := `induction_eliminator}]
end SparseRecursor
