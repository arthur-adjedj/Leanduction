import Lean
import Leanduction.NestedPositivity
import Leanduction.SparseParametricity

open Lean Elab Meta

namespace SparseRecursor

def replaceNestedMotives (indVals : List InductiveVal) (realMotives : Array Expr) (nestedMotives : Array Expr) : MetaM (Array Expr) := do
  go 0 #[]
where
  go (i : Nat) (acc : Array Expr) : MetaM (Array Expr) :=
    if _ : i < nestedMotives.size then do
      forallTelescope (← inferType nestedMotives[i]) fun xs ty => do
        let majorTy ← inferType xs[xs.size-1]!
      -- TODO
      sorry
    else
      return acc

-- TODO generate the term at the same time (amounts to instantiating the nestedMotives with the sparseForNestedMotives)
def type (indName : Name) : MetaM Expr := do
  let info ← getConstInfoInduct indName
  let indVals ← info.all.mapM getConstInfoInduct
  let recInfo ← getConstInfoRec (info.name ++ `rec)
  forallTelescope recInfo.type fun xs ty => do
    let params := xs[0...info.numParams]
    let indices_and_major := xs[recInfo.getFirstIndexIdx...xs.size]
    let motives := xs[info.numParams...info.numParams + info.all.length]
    let nestedMotives := xs[(info.numParams + info.all.length)...recInfo.getFirstMinorIdx]
    let sparseForNestedMotives ←  replaceNestedMotives indVals motives nestedMotives
    let numMinors := indVals.foldl (init := 0) (fun acc ind => acc + ind.ctors.length)
    let oldMinors := xs[recInfo.getFirstMinorIdx...recInfo.getFirstMinorIdx + numMinors]
    let minors := oldMinors.toArray.map (Expr.replaceFVars · nestedMotives sparseForNestedMotives)
    let ty ← mkForallFVars indices_and_major ty
    let ty ← mkForallFVars minors ty
    let ty ← mkForallFVars motives ty
    let ty ← mkForallFVars params ty
    return ty

end SparseRecursor
