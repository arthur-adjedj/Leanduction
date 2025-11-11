import Lean
import Leanduction.SparseParametricity

open Lean Elab Meta
open NestedPositivity
open SparseParametricityTranslation


elab "#gen_sparse" t:term : command => Command.liftTermElabM do
  let t ← Term.elabTerm t none
  let e ← addSparseTranslation t.constName!
  logInfo m!"{e}"

inductive Tree (α : Type) where
  | node : List (Tree α) → Tree α

set_option Elab.async false

#gen_sparse List
set_option pp.universes true
#print List.Sparse
#gen_sparse Tree

-- run_cmd Command.liftTermElabM do
  -- let tparse ← getConstInfoRec ``Tree.Sparse.rec
  -- for rule in tparse.rules do
  -- logInfo m!"{rule.rhs}"
#check List.Sparse

-- set_option genSizeOfSpec false
-- inductive Tree.Sparse (α : Type) (P : α → Type u): Tree α → (Type u) where
  -- | Tree.Sparse.node : (a : List (Tree α)) → List.Sparse (Tree α) (fun z => Tree.Sparse α P z) a → Tree.Sparse α P (Tree.node a)

#print Tree.Sparse
--
noncomputable def Tree.rec' {α : Type} {motive_1 : Tree α → Prop}
  (node : (a : List (Tree α)) → List.Sparse (Tree α) motive_1 a → motive_1 (Tree.node a)) (t : Tree α) : motive_1 t :=
@Tree.rec α motive_1 (List.Sparse (Tree α) motive_1) node (List.Sparse.nil _ _) (List.Sparse.cons _ _) t
