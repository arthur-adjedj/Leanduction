module

public meta import Leanduction.Util
public meta import Leanduction.NestedPositivity
public meta import Leanduction.SparseParametricity

open Lean Elab Meta
open Parser.Tactic (optConfig)

meta section

namespace SparseRecursor

public structure Config where
  indElim : Bool := true

declare_command_config_elab elabSparseConfig SparseRecursor.Config
public partial def replaceNestedMotivesAndMinors (indVals : List InductiveVal) (realMotives : Array Expr) (nestedMotives : Array Expr) : MetaM (Array Expr × Array Expr) := do
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
        return (ty.tryEtaReduce,minors)
      trace[Leanduction.Recursor] m!"nestedMotive : {nestedMotiveAndMinors}"
      go (i+1) (motivesReplacements.push nestedMotiveAndMinors.1) (minorsReplacements.append nestedMotiveAndMinors.2)
    else
      return (motivesReplacements,minorsReplacements)

  nestedMotiveAndMinors (motiveType : Expr) (noMinors : Bool) : MetaM (if noMinors then Expr else Expr × Array Expr) := do
    trace[Leanduction.Recursor] m!"nestedMotive {motiveType}"
    motiveType.withApp fun fn args =>  do
      let nestedIndName := fn.constName!
      let nestedIndVal ← getConstInfoInduct nestedIndName
      let nestedParams := args[0:nestedIndVal.numParams].toArray
      let nestedParamsMask ← NestedPositivity.positiveParams nestedIndVal
      let sparseNestedIndName := SparseParametricityTranslation.sparseName fn.constName!
      let ty := mkAppN (mkConst sparseNestedIndName fn.constLevels!) nestedParams
      let preds ← nestedParams.mapIdxM fun idx e => if nestedParamsMask[idx]! then return some (← genPred e) else pure none
      let ty := mkAppN ty (preds.filterMap id)
      let ty := mkAppN ty args[nestedIndVal.numParams:]
      match noMinors with
        | true => return ty
        | false => do
          let sparseNestedIndVal ← getConstInfoInduct sparseNestedIndName
          let minors ← sparseNestedIndVal.ctors.toArray.mapM (genMinorOf fn.constLevels! nestedParams preds)
          return (ty,minors)

  genMinorOf (lvl : List Level) (nestedParams : Array Expr) (preds : Array (Option Expr)) (ctorName : Name) : MetaM Expr := do
    let te := mkAppN (mkAppN (mkConst ctorName lvl) nestedParams) (preds.filterMap id)
    forallTelescope (← inferType te) fun xs _ => do
      let trivialProofsMask : Array (Bool × Expr) ← xs.mapM fun e => do
        forallTelescopeReducing (← inferType e) fun xs ty => do if ty.isTrue then pure (true, ← mkLambdaFVars xs (mkConst `True.intro)) else pure (false,e)
      let teArgs := trivialProofsMask.map (·.2)
      let te := mkAppN te teArgs
      let xs := trivialProofsMask.filterMap (fun | (false,e) => some e | _ => none)
      let te ← mkLambdaFVars xs te
      return te.tryEtaReduce

  genPred (param : Expr) : MetaM Expr := do
    trace[Leanduction.Recursor] m!"genPred {param}"
    withLocalDeclD `p param fun f => do
      forallTelescope param fun xs ty => do
        let fallback := do mkLambdaFVars xs (← mkLambdaFVars #[f] (mkConst `True))
        if !(param.getUsedConstants.any indVals[0]!.all.contains) then
          return (← fallback)
        ty.withApp fun fn args => do
          let fnName := fn.constName!
          if let some indIdx := indVals[0]!.all.findIdx? (· == fnName) then
            let ty := realMotives[indIdx]!
            let ty := mkAppN ty args[indVals[indIdx]!.numParams:]
            let ty := mkApp ty (mkAppN f xs)
            let ty ← mkForallFVars xs ty
            let motive ← mkLambdaFVars #[f] ty
            return motive.tryEtaReduce
          else
            let ty ← nestedMotiveAndMinors ty true
            let ty := mkApp ty (mkAppN f xs)
            let ty ← mkForallFVars xs ty
            let motive ← mkLambdaFVars #[f] ty
            return motive.tryEtaReduce

/--Generate the sparse recursor for an inductive type `Ind` using `#gen_sparse_rec Ind`.
This recursor is then used by the `induction` tactic, which usually fails when trying to induct on nested inductive types.
To provide a custom name `indrec` to the recursor, use `#gen_sparse_rec Ind as indrec`
If you do not want the `induction` tactic to make use of the generated recursor by default, use `#gen_sparse_rec -indElim Ind`.

Example:
```
inductive Tree (α : Type) :  Type where
  | node : α → List (Tree α) → Tree α

#gen_sparse_rec Tree

def Tree.map (f : α → β) : Tree α → Tree β
  | node x children => .node (f x) (children.map (Tree.map f))

example (t : Tree α) : t.map id = t := by
  induction t with --uses the generated sparse recursor instead of failing
  | node x children cih =>
    rw [Tree.map]
    congr
    induction cih <;> simp [*]
```
-/
public def genSparseRec (cfg : Config) (indName sparseRecName: Name) : TermElabM Unit := do
  checkConstant sparseRecName
  let info ← getConstInfoInduct indName
  SparseParametricityTranslation.genNeededSparseTranslations info
  let indVals ← info.all.mapM getConstInfoInduct
  let recName := info.name ++ `rec
  let recInfo ← getConstInfoRec recName
  let recTypeToProp := match recInfo.levelParams with
    | [] => recInfo.type
    | motiveUniv::_ => recInfo.type.instantiateLevelParams [motiveUniv] [0]
  forallTelescope recTypeToProp fun xs ty => do
    let params := xs[0:info.numParams]
    let indices_and_major := xs[recInfo.getFirstIndexIdx:]
    let motives := xs[info.numParams:info.numParams + info.all.length]
    let nestedMotives := xs[(info.numParams + info.all.length):recInfo.getFirstMinorIdx]
    let (sparseForNestedMotives,nestedsMinors) ← replaceNestedMotivesAndMinors indVals motives nestedMotives
    trace[Leanduction.Recursor] m!"sparseForNestedMotives : {sparseForNestedMotives}"
    let numMinors := indVals.foldl (init := 0) (fun acc ind => acc + ind.ctors.length)
    let oldMinors := xs[recInfo.getFirstMinorIdx:recInfo.getFirstMinorIdx + numMinors]
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
      trace[Leanduction.Recursor] m!"term : {te}"
      Meta.check te
      addDecl <| .defnDecl {
        name := sparseRecName
        levelParams := match recInfo.levelParams with | [] => [] | _::tl => tl
        type := ty
        value := te
        hints := .regular 0 --TODO figure out how important that is ?
        safety := .safe
        }
      if cfg.indElim then
        Term.applyAttributes sparseRecName #[{name := `induction_eliminator}]

@[inherit_doc genSparseRec]
syntax "#gen_sparse_rec" optConfig ident ("as" ident)? : command

elab_rules : command
  | `(command| #gen_sparse_rec $cfg:optConfig $indName:ident $[as $recName:ident]? ) => do
  let cfg ← elabSparseConfig cfg
  let indName := indName.getId
  let sparseRecName := recName.map TSyntax.getId |>.getD (indName ++ `rec_sparse)
  Command.liftTermElabM <| SparseRecursor.genSparseRec cfg indName sparseRecName

end SparseRecursor

initialize
  registerTraceClass `Leanduction.Recursor (inherited := true)
