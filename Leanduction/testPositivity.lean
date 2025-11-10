import Lean
import Leanduction.SparseParametricity

open Lean Elab Meta
open NestedPositivity
open SparseParametricityTranslation


elab "#gen_sparse" t:term : command => Command.liftTermElabM do
  let t ← Term.elabTerm t none
  let e ← addSparseTranslation t.constName!
  logInfo m!"{e}"

inductive Ok1 where
  | mk : id Ok1 → Ok1

axiom T : Type → Type

inductive Ok2 where
  | mk : List Ok2 → Ok2

inductive Nest1 (A : Type 1) where
  | mk : Option (Nat → A) → Nest1 A

#gen_sparse Option
#check Option.Sparse

#gen_sparse Nest1

inductive Nest5 (f : Nat → Type) where
  | mk : (Nat → Option (Nat → f 5)) → Nest5 f

#gen_sparse Nest5
#print Nest5.Sparse

inductive Ok5 : Nat → Type where
  | mk : Nest5 Ok5 → Ok5 n

#gen_sparse Ok5

inductive Nest6 (f : Nat → Type) where
  | mk : f n → Nest6 f

#gen_sparse Nest6

inductive Ok6 : Nat → Type where
  | mk : Nest6 Ok6 → Ok6 n

#gen_sparse Ok6

inductive Nest7 (n : Nat) (f : Nat → Type) where
  | mk : f n → Nest7 n f

#gen_sparse Nest7

inductive Good7 (n : Nat) : Nat → Type where
  | mk : Nest7 n (Good7 n) → Good7 n n

#gen_sparse Good7

inductive Nest8 (α : Type) : (β : Type) → Type  where
  | mk : α → Nest8 α Bool

#gen_sparse Nest8

inductive Ok8 : Type where
  | mk : Nest8 Ok8 Unit → Ok8

#gen_sparse Ok8

inductive Nest9 (α : Type) : Type  where
  | mk : (α → α) → Nest9 α

#gen_sparse Nest9

inductive Nest10 (α : Type) : Type  where
  | mk : α  → Nest10 α

#gen_sparse Nest10

inductive Ok10 where
  | mk : Nest10 (Bool -> Ok10) → Ok10

inductive Nest11 (α : Bool → Type) : Type  where
  | mk : α true → Nest11 α

#gen_sparse Nest11
