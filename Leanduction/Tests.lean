import Lean
import Leanduction.SparseParametricity
import Leanduction.SparseRecursor

open Lean Elab Meta
open NestedPositivity
open SparseParametricityTranslation


elab "#gen_sparse" t:term : command => Command.liftTermElabM do
  let t ← Term.elabTerm t none
  let e ← addSparseTranslation t.constName!
  logInfo m!"{e}"

elab "#gen_sparse_rec" t:term : command => Command.liftTermElabM do
  let t ← Term.elabTerm t none
  let e ← SparseRecursor.type t.constName!
  logInfo m!"{e}"

#gen_sparse Option
#gen_sparse List
#gen_sparse_rec List

inductive Weird (α : Type) : Nat → Type where
  | node : (Int → Option (Int → List (Int → Weird α 0))) → Weird α 0

#check List.Sparse

#gen_sparse Weird

#gen_sparse_rec Weird

inductive Tree (α : Type) : Type where
  | node : (a : List (Tree α)) → Tree α

#print Tree.Sparse

noncomputable def Tree.rec' {α : Type} {motive_1 : Tree α → Prop}
  (node : (a : List (Tree α)) → List.Sparse (Tree α) motive_1 a → motive_1 (Tree.node a)) (t : Tree α) : motive_1 t :=
@Tree.rec α motive_1 (List.Sparse (Tree α) motive_1) node (List.Sparse.nil (Tree α) motive_1) (List.Sparse.cons (Tree α) motive_1) t
