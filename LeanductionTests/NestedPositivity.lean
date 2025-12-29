import Leanduction.NestedPositivity
import Lean
open Lean



elab "#get_mask"  i:ident : command => do
  let indName := i.getId
  let indVal ← getConstInfoInduct indName
  let mask ← Elab.Command.liftTermElabM <| NestedPositivity.positiveParams indVal
  logInfo m!"{mask}"


/-- info: [true] -/
#guard_msgs in
#get_mask Option

/-- info: [true] -/
#guard_msgs in
#get_mask List

/-- info: [true] -/
#guard_msgs in
#get_mask Array

inductive Weird (α : Type) : Nat → Type where
  | node n : (Int → Option (Int → List (Int → Weird α 0))) → Weird α n

/-- info: [true] -/
#guard_msgs in
#get_mask Weird

namespace Test2
inductive Foo (α : Type) where
  | bad : (α → α) → Foo α

/-- info: [false] -/
#guard_msgs in
#get_mask Test2.Foo
end Test2

inductive Foo (A B : Type) where
  | foo : A -> B -> Foo A B

inductive Bar (A : Type) where
  | bar : Foo (Bar A) Nat → Bar A

/-- info: [true, true] -/
#guard_msgs in
#get_mask Foo

/-- info: [true] -/
#guard_msgs in
#get_mask Bar

inductive Tree' where
  | node : List Tree' → Tree'

/-- info: [] -/
#guard_msgs in
#get_mask Tree'

mutual
  inductive Mut1 (A : Type) where
    | foo : Mut2 A -> Mut1 A
    | foz : List (Mut2 A) -> Mut1 A

  inductive Mut2 (A : Type) where
    | bar :  Mut1 A -> Mut2 A
end

/-- info: [true] -/
#guard_msgs in
#get_mask Mut1


inductive Ok1 where
  | mk : id Ok1 → Ok1

axiom T : Type → Type

inductive Ok2 where
  | mk : List Ok2 → Ok2

inductive Nest1 (A : Type 1) where
  | mk : Option (Nat → A) → Nest1 A

/-- info: [true] -/
#guard_msgs in
#get_mask Nest1

inductive Nest5 (f : Nat → Type) where
  | mk : (Nat → Option (Nat → f 5)) → Nest5 f

/-- info: [true] -/
#guard_msgs in
#get_mask Nest5

inductive Ok5 : Nat → Type where
  | mk : Nest5 Ok5 → Ok5 n

/-- info: [] -/
#guard_msgs in
#get_mask Ok5

inductive Nest6 (f : Nat → Type) where
  | mk : f n → Nest6 f

/-- info: [true] -/
#guard_msgs in
#get_mask Nest6

inductive Ok6 : Nat → Type where
  | mk : Nest6 Ok6 → Ok6 n

/-- info: [] -/
#guard_msgs in
#get_mask Ok6

inductive Nest7 (n : Nat) (f : Nat → Type) where
  | mk : f n → Nest7 n f

/-- info: [false, true] -/
#guard_msgs in
#get_mask Nest7

inductive Good7 (n : Nat) : Nat → Type where
  | mk : Nest7 n (Good7 n) → Good7 n n

/-- info: [false] -/
#guard_msgs in
#get_mask Good7

inductive Nest8 (α : Type) : (β : Type) → Type  where
  | mk : α → Nest8 α Bool

/-- info: [true] -/
#guard_msgs in
#get_mask Nest8

inductive Ok8 : Type where
  | mk : Nest8 Ok8 Unit → Ok8

/-- info: [] -/
#guard_msgs in
#get_mask Ok8

inductive Nest9 (α : Type) : Type  where
  | mk : (α → α) → Nest9 α

/-- info: [false] -/
#guard_msgs in
#get_mask Nest9

inductive Nest10 (α : Type) : Type  where
  | mk : α  → Nest10 α

/-- info: [true] -/
#guard_msgs in
#get_mask Nest10

inductive Ok10 where
  | mk : Nest10 (Bool -> Ok10) → Ok10

inductive Nest11 (α : Bool → Type) : Type  where
  | mk : α true → Nest11 α

/-- info: [true] -/
#guard_msgs in
#get_mask Nest11

inductive Higher (f : Type → Type) (A : Type) where
 | c_higher : f A → Higher f A

/-- info: [true, false] -/
#guard_msgs in
#get_mask Higher
