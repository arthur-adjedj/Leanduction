import Leanduction.SparseParametricity
import Leanduction.SparseRecursor

inductive Weird (α : Type) : Nat → Type where
  | node : (Int → Option (Int → List (Int → Weird α 0))) → Weird α 0

-- #gen_sparse_rec Weird

set_option trace.Sparse.Recursor true

inductive Tree (α : Type) :  Type where
  | node : α → (a : List (Tree α)) → Tree α

-- #gen_sparse Tree
#gen_sparse_rec Tree

def Tree.map (f : α → β) : Tree α → Tree β
  | node x children => .node (f x) (children.map (Tree.map f))

#print List.All

example (t : Tree α) : t.map id = t := by
  induction t with
  | node x children cih =>
    rw [Tree.map]
    congr
    induction cih <;> simp [*]
