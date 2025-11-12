import Leanduction.SparseParametricity
import Leanduction.SparseRecursor

-- TODO add better examples

#gen_sparse Option
#gen_sparse List
#gen_sparse_rec List

inductive Weird (α : Type) : Nat → Type where
  | node : (Int → Option (Int → List (Int → Weird α 0))) → Weird α 0

#gen_sparse Weird

#gen_sparse_rec Weird

inductive Tree (α : Type) : Type where
  | node : α → (a : List (Tree α)) → Tree α

#gen_sparse Tree
#gen_sparse_rec Tree

def Tree.map (f : α → β) : Tree α → Tree β
  | node x children => .node (f x) (children.map (Tree.map f))

example (t : Tree α) : t.map id = t := by
  induction t with
  | node x children cih =>
    rw [Tree.map]
    congr
    induction cih
    · rfl
    · simp [*]

inductive Foo (α : Type) where
  | bad : (α → α) → Foo α
