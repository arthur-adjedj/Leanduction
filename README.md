# Leanduction

This small library generates recursors for nested inductive types that are usable by the `induction` tactic
It works as follows:
given a nested inductive type, e.g
```lean
inductive Tree (α : Type) : Type where
  | node : α → (a : List (Tree α)) → Tree α
```

First, use `#gen_sparse` to generate sparse parametricity translations for your nested types, e.g here for `List`:
```lean
#gen_sparse List
/-List.Sparse.{u} (α : Type u) (P : α → Prop) : List α → Prop-/
#check List.Sparse 
```
Then, you can generate a recursor for your type using `#gen_sparse_rec` as follows:
```lean
#gen_sparse_rec Tree
/-Tree.rec_sparse {α : Type} {motive_1 : Tree α → Prop}
  (node : ∀ (a : α) (a_1 : List (Tree α)), List.Sparse (Tree α) motive_1 a_1 → motive_1 (Tree.node a a_1))
  (t : Tree α) : motive_1 t-/
#check Tree.rec_sparse
```

When using the `induction` tactic on `Tree`s, this recursor will now always be used by default, allowing the tactic to succeed:
```lean
def Tree.map (f : α → β) : Tree α → Tree β
  | node x children => .node (f x) (children.map (Tree.map f))

example (t : Tree α) : t.map id = t := by
  induction t with
  | node x children cih =>
    rw [Tree.map]
    congr
    induction cih <;> simp [*]
```