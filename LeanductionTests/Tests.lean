import Leanduction
import Lean
open Lean

elab "#get_mask"  i:ident : command => do
  let indName := i.getId
  let indVal ← getConstInfoInduct indName
  let mask ← Elab.Command.liftTermElabM <| NestedPositivity.positiveParams indVal
  logInfo m!"Mask : {mask}"

open Elab Command in
elab "#gen_mask_rec" i:ident : command => do
  let mask ← `(command| #get_mask $i)
  let genSparse ← `(command| #gen_sparse $i)
  let genSparseRec ← `(command| #gen_sparse_rec $i:ident)
  [mask,genSparse, genSparseRec].forM (elabCommand ·)

#guard_msgs (error, drop all) in
#gen_mask_rec Option

#guard_msgs (error, drop all) in
#gen_mask_rec List

#guard_msgs (error, drop all) in
#gen_mask_rec Array

inductive Weird (α : Type) : Nat → Type where
  | node n : (Int → Option (Int → List (Int → Weird α 0))) → Weird α n

#guard_msgs (error, drop all) in
#gen_mask_rec Weird

namespace Test2
inductive Foo (α : Type) where
  | bad : (α → α) → Foo α

#guard_msgs (error, drop all) in
#gen_mask_rec Test2.Foo
end Test2

inductive Foo (A B : Type) where
  | foo : A -> B -> Foo A B

inductive Bar (A : Type) where
  | bar : Foo (Bar A) Nat → Bar A

#guard_msgs (error, drop all) in
#gen_mask_rec Foo

#guard_msgs (error, drop all) in
#gen_mask_rec Bar

inductive Tree' where
  | node : List Tree' → Tree'

#guard_msgs(error, drop all) in
#gen_mask_rec Tree'

mutual
  inductive Mut1 (A : Type) where
    | foo : Mut2 A -> Mut1 A
    | foz : List (Mut2 A) -> Mut1 A

  inductive Mut2 (A : Type) where
    | bar :  Mut1 A -> Mut2 A
end

#guard_msgs (error, drop all) in
#gen_mask_rec Mut1


/--
error: failed to generate `SizeOf` instance for `Ok1`:
  type mismatch
-/
#guard_msgs (error, drop all) in
inductive Ok1 where
  | mk : id Ok1 → Ok1

axiom T : Type → Type

inductive Ok2 where
  | mk : List Ok2 → Ok2

inductive Nest1 (A : Type 1) where
  | mk : Option (Nat → A) → Nest1 A

#guard_msgs (error, drop all) in
#gen_mask_rec Nest1

inductive Nest5 (f : Nat → Type) where
  | mk : (Nat → Option (Nat → f 5)) → Nest5 f

#guard_msgs (error, drop all) in
#gen_mask_rec Nest5

inductive Ok5 : Nat → Type where
  | mk : Nest5 Ok5 → Ok5 n

#guard_msgs (error, drop all) in
#gen_mask_rec Ok5

inductive Nest6 (f : Nat → Type) where
  | mk : f n → Nest6 f

#guard_msgs (error, drop all) in
#gen_mask_rec Nest6

inductive Ok6 : Nat → Type where
  | mk : Nest6 Ok6 → Ok6 n

#guard_msgs (error, drop all) in
#gen_mask_rec Ok6

inductive Nest7 (n : Nat) (f : Nat → Type) where
  | mk : f n → Nest7 n f

#guard_msgs (error, drop all) in
#gen_mask_rec Nest7

inductive Good7 (n : Nat) : Nat → Type where
  | mk : Nest7 n (Good7 n) → Good7 n n

#guard_msgs (error, drop all) in
#gen_mask_rec Good7

inductive Nest8 (α : Type) : (β : Type) → Type where
  | mk : α → Nest8 α Bool

#guard_msgs (error, drop all) in
#gen_mask_rec Nest8

inductive Ok8 : Type where
  | mk : Nest8 Ok8 Unit → Ok8

#guard_msgs (error, drop all) in
#gen_mask_rec Ok8

inductive Nest9 (α : Type) : Type  where
  | mk : (α → α) → Nest9 α

#guard_msgs (error, drop all) in
#gen_mask_rec Nest9

inductive Nest10 (α : Type) : Type  where
  | mk : α  → Nest10 α

#guard_msgs (error, drop all) in
#gen_mask_rec Nest10

inductive Ok10 where
  | mk : Nest10 (Bool -> Ok10) → Ok10

inductive Nest11 (α : Bool → Type) : Type  where
  | mk : α true → Nest11 α

#guard_msgs (error, drop all) in
#gen_mask_rec Nest11

inductive Higher (f : Type → Type) (A : Type) where
 | c_higher : f A → Higher f A

#guard_msgs (error, drop all) in
#gen_mask_rec Higher
