import Leanduction
import LeanductionTests.Tests

namespace Examples

inductive Tree (α : Type) :  Type where
  | node : α → (a : List (Tree α)) → Tree α

#gen_sparse_rec Tree

/--
info: Examples.Tree.rec_sparse {α : Type} {motive_1 : Tree α → Prop}
  (node : ∀ (a : α) (a_1 : List (Tree α)), List.All (Tree α) motive_1 a_1 → motive_1 (Tree.node a a_1)) (t : Tree α) :
  motive_1 t
-/
#guard_msgs in
#check Tree.rec_sparse

def Tree.map (f : α → β) : Tree α → Tree β
  | node x children => .node (f x) (children.map (Tree.map f))

example (t : Tree α) : t.map id = t := by
  induction t with
  | node x children cih =>
    rw [Tree.map]
    congr
    induction cih <;> simp [*]
end Examples
