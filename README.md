# Leanduction

This small library generates recursors for nested inductive types that are usable by the `induction` tactic
It works as follows:
given a nested inductive type, e.g
```lean
inductive Tree (α : Type) : Type where
  | node : α → (a : List (Tree α)) → Tree α
```

You can generate a recursor for your type using `#gen_sparse_rec` as follows:
```lean
#gen_sparse_rec Tree
/-Tree.rec_sparse {α : Type} {motive_1 : Tree α → Prop}
  (node : ∀ (a : α) (a_1 : List (Tree α)), List.All (Tree α) motive_1 a_1 → motive_1 (Tree.node a a_1))
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

The algorithms used in this library are described in the following research article:
> Thomas Lamiaux, Yannick Forster, Matthieu Sozeau, and Nicolas Tabareau. 2026. Nested Inductive Types: Justified and Usable Nested Inductive Types in Lean and Rocq. Proc. ACM Program. Lang. 10, PLDI, Article 244 (June 2026), 24 pages. https://doi.org/10.1145/3808322


## Missing feature(s):

The generated recursors currently only eliminate to `Prop` rather than arbitrary `Sort`s like the usual recursors. Avoiding this issue would imply inserting various `ULift`s inside the generated recursors' signatures, which would make their uses in proofs more cumbersome. 