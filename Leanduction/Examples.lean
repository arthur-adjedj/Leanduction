import Leanduction.SparseParametricity
import Leanduction.SparseRecursor

inductive Weird (α : Type) : Nat → Type where
  | node n : (Int → Option (Int → List (Int → Weird α 0))) → Weird α n

#gen_sparse_rec -indElim Weird as Weird.s

inductive Tree (α : Type) :  Type where
  | node : α → (a : List (Tree α)) → Tree α

#gen_sparse_rec Tree

def Tree.map (f : α → β) : Tree α → Tree β
  | node x children => .node (f x) (children.map (Tree.map f))

example (t : Tree α) : t.map id = t := by
  induction t with
  | node x children cih =>
    rw [Tree.map]
    congr
    induction cih <;> simp [*]
