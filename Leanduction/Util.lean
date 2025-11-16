import Lean

open Lean Elab Meta

def checkConstant (name : Name): MetaM Unit := do
  if (← getEnv).contains name then
    throwError "`{.ofConstName name true}` has already been declared"

/-- Transforms expressions of shape `fun x => f x` to `f` when x doesn't appear in `f`, useful to generate better looking recursors-/
partial def Lean.Expr.tryEtaReduce (e: Expr): Expr :=
  match e with
    | .lam _ _ (.app f (.bvar 0)) _ => if f.hasLooseBVar 0 then e else f |>.lowerLooseBVars 0 1 |>.tryEtaReduce
    | _ => e
