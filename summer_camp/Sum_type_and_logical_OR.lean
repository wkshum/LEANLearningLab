namespace LectureSum

/-1. Defining our own sum type

The sum type represents "either A or B".

If
    A : Type
    B : Type

then
    Sum A B : Type

is the type whose elements are either:
    - an element of A, put into the left side, or
    - an element of B, put into the right side.

Lean already has a built-in `Sum`, so we define our own version
inside a namespace.
-/

inductive MySum (A B : Type) : Type where
  | inl (a : A) : MySum A B
  | inr (b : B) : MySum A B

#check MySum
-- MySum : Type → Type → Type

#check MySum.inl
-- MySum.inl : {A B : Type} → A → MySum A B

#check MySum.inr
-- MySum.inr : {A B : Type} → B → MySum A B


/-
Examples of constructing elements of a sum type.
-/

def s0 : MySum Nat Bool :=
  MySum.inl 37

def s1 : MySum Nat Bool :=
  MySum.inr true

#check s0  -- s0 : MySum Nat Bool

#check s1  -- s1 : MySum Nat Bool


/-
A term of type `MySum Nat Bool` is either:
    MySum.inl n

for some `n : Nat`, or
    MySum.inr b

for some `b : Bool`.

So `MySum A B` is a data-level "either/or".
-/


/-  2. Eliminating a sum type

To define a function out of `MySum A B`, we must say what to do
in both cases:

    1. If the input is `MySum.inl a`, what should we return?
    2. If the input is `MySum.inr b`, what should we return?

So to define:
    MySum A B → C

it is enough to provide:
    A → C
    B → C

This is the elimination principle for sums.
-/

def sumToString : MySum Nat Bool → String
  | MySum.inl n => "left Nat: " ++ toString n
  | MySum.inr b => "right Bool: " ++ toString b

#eval sumToString s0  -- "left Nat: 37"

#eval sumToString s1  -- "right Bool: true"


/-
General eliminator for `MySum`.

Given:
    f : A → C
    g : B → C

we get:
    MySum A B → C
-/

def sumElim {A B C : Type}
    (f : A → C)
    (g : B → C) :
    MySum A B → C
  | MySum.inl a => f a
  | MySum.inr b => g b


/-
Examples:
-/

def sumNatBoolToNat : MySum Nat Bool → Nat :=
  sumElim
    (fun n => n + 1)
    (fun b => if b then 1 else 0)

#eval sumNatBoolToNat (MySum.inl 10)  -- 11

#eval sumNatBoolToNat (MySum.inr true)  -- 1

#eval sumNatBoolToNat (MySum.inr false)  -- 0


/-
Computation rules.

When we eliminate a left value, we use the left branch.
When we eliminate a right value, we use the right branch.
-/

example {A B C : Type} (f : A → C) (g : B → C) (a : A) :
    sumElim f g (MySum.inl a : MySum A B) = f a := by
  rfl

example {A B C : Type} (f : A → C) (g : B → C) (b : B) :
    sumElim f g (MySum.inr b : MySum A B) = g b := by
  rfl


/- 3. Pattern matching on sums

A sum type has two constructors, so to use an element of a sum type,
we normally use pattern matching.

This is different from a product type.

For a product:
    you get both components.

For a sum:
    you must consider both possible cases.
-/

def describeSum : MySum String Nat → String
  | MySum.inl s => "I got a string: " ++ s
  | MySum.inr n => "I got a number: " ++ toString n

#eval describeSum (MySum.inl "hello")
-- "I got a string: hello"

#eval describeSum (MySum.inr 42)
-- "I got a number: 42"


/- 4. Sum type is commutative up to equivalence

From A + B, we can construct B + A by swapping the two cases.
-/

def sumComm {A B : Type} : MySum A B → MySum B A
  | MySum.inl a => MySum.inr a
  | MySum.inr b => MySum.inl b

example :
    sumComm (MySum.inl 5 : MySum Nat Bool) = MySum.inr 5 := by
  rfl

example :
    sumComm (MySum.inr true : MySum Nat Bool) = MySum.inl true := by
  rfl


/-
Swapping twice gives back the original value.
-/

theorem sumComm_sumComm {A B : Type} (x : MySum A B) :
    sumComm (sumComm x) = x := by
  cases x with
  | inl a =>
      rfl
  | inr b =>
      rfl


/- 5. Sum type and functions

A function out of a sum type

    MySum A B → C

is equivalent to a pair of functions

    A → C
    B → C

This is the universal property of coproducts.
-/

structure Prod (A B : Type) where
  fst : A
  snd : B


def sumToProdOfFunctions {A B C : Type} :
    (MySum A B → C) → Prod (A → C) (B → C) :=
  fun h =>
    Prod.mk
      (fun a => h (MySum.inl a))
      (fun b => h (MySum.inr b))


def prodOfFunctionsToSum {A B C : Type} :
    Prod (A → C) (B → C) → MySum A B → C :=
  fun p x =>
    match x with
    | MySum.inl a => p.fst a
    | MySum.inr b => p.snd b


/-
Computation examples.
-/

example {A B C : Type} (f : A → C) (g : B → C) (a : A) :
    prodOfFunctionsToSum (Prod.mk f g) (MySum.inl a) = f a := by
  rfl

example {A B C : Type} (f : A → C) (g : B → C) (b : B) :
    prodOfFunctionsToSum (Prod.mk f g) (MySum.inr b) = g b := by
  rfl


/-  6. Logical analogue: OR

Under Curry--Howard:
    Sum type corresponds to logical OR.

At the type level:
    MySum A B

means data that is either from A or from B.

At the proposition level:
    MyOr P Q

means a proof of P or a proof of Q.

To prove `P OR Q`, we either give:
    - a proof of P, using the left constructor, or
    - a proof of Q, using the right constructor.
-/

inductive MyOr (P Q : Prop) : Prop where
  | inl (p : P) : MyOr P Q
  | inr (q : Q) : MyOr P Q

#check MyOr
-- MyOr : Prop → Prop → Prop

#check MyOr.inl
-- MyOr.inl : {P Q : Prop} → P → MyOr P Q

#check MyOr.inr
-- MyOr.inr : {P Q : Prop} → Q → MyOr P Q


/-
Examples of proving an OR.
-/

example : MyOr (2 = 2) (3 = 4) :=
  MyOr.inl rfl

example : MyOr (2 = 3) (4 = 4) :=
  MyOr.inr rfl


/-
Notice the difference from AND.

To prove P AND Q, we need both:
    p : P
    q : Q

To prove P OR Q, we need only one:
    either p : P
    or     q : Q

But we must specify which side we are using.
-/


/-  7. Eliminating OR

To use a proof of `MyOr P Q`, we must consider both cases.

If we want to prove R from MyOr P Q, we need:
    P → R
    Q → R

Then from MyOr P Q we get R.

This is proof by cases.
-/

def orElim {P Q R : Prop}
    (hp : P → R)
    (hq : Q → R) :
    MyOr P Q → R
  | MyOr.inl p => hp p
  | MyOr.inr q => hq q


/-
Example: OR is commutative.
-/

def orComm {P Q : Prop} : MyOr P Q → MyOr Q P :=
  orElim
    (fun p => MyOr.inr p)
    (fun q => MyOr.inl q)


example {P Q : Prop} (h : MyOr P Q) : MyOr Q P :=
  orComm h


/-
Computation rules for OR elimination.
-/

example {P Q R : Prop} (hp : P → R) (hq : Q → R) (p : P) :
    orElim hp hq (MyOr.inl p : MyOr P Q) = hp p := by
  rfl

example {P Q R : Prop} (hp : P → R) (hq : Q → R) (q : Q) :
    orElim hp hq (MyOr.inr q : MyOr P Q) = hq q := by
  rfl


/- 8. OR and implication

The logical eliminator says:
    (P ∨ Q → R) is equivalent to ((P → R) ∧ (Q → R))

This is the logical version of the universal property of coproducts.
-/

structure MyAnd (P Q : Prop) : Prop where
  fst : P
  snd : Q


def orToAndOfImplications {P Q R : Prop} :
    (MyOr P Q → R) → MyAnd (P → R) (Q → R) :=
  fun h =>
    MyAnd.mk
      (fun p => h (MyOr.inl p))
      (fun q => h (MyOr.inr q))


def andOfImplicationsToOr {P Q R : Prop} :
    MyAnd (P → R) (Q → R) → MyOr P Q → R :=
  fun h x =>
    match x with
    | MyOr.inl p => h.fst p
    | MyOr.inr q => h.snd q


/-
Examples:
-/

example {P Q R : Prop} (hp : P → R) (hq : Q → R) :
    MyOr P Q → R :=
  andOfImplicationsToOr (MyAnd.mk hp hq)


example {P Q R : Prop} (h : MyOr P Q → R) :
    MyAnd (P → R) (Q → R) :=
  orToAndOfImplications h


/-  9. Relation with False and Empty

At the type level, the empty type has no constructors.

At the logical level, False has no proofs.

They are the zero/initial objects.
-/

inductive MyEmpty : Type where

inductive MyFalse : Prop where


/-
From MyEmpty, we can define a function to any type.
This is because there are no cases to check.

The meaning of `nomatch` is:
there are no possible cases for e,
because MyEmpty has no constructors
-/

def emptyElim {A : Type} : MyEmpty → A :=
  fun e => nomatch e



/-
From MyFalse, we can prove any proposition.
This is called "ex falso quodlibet" in Latin
-/

def falseElim {P : Prop} : MyFalse → P :=
  fun h => nomatch h


/-
Empty is identity for sums:
    A + Empty ≅ A
    Empty + A ≅ A

False is identity for OR:
    P ∨ False ↔ P
    False ∨ P ↔ P
-/


/-
Map from A + Empty to A.
-/

def sumEmptyToA {A : Type} : MySum A MyEmpty → A
  | MySum.inl a => a
  | MySum.inr e => emptyElim e


/-
Map from A to A + Empty.
-/

def aToSumEmpty {A : Type} : A → MySum A MyEmpty :=
  fun a => MySum.inl a


example {A : Type} (a : A) :
    sumEmptyToA (aToSumEmpty a) = a := by
  rfl

/-
Map from Empty + A to A.
-/

def emptySumToA {A : Type} : MySum MyEmpty A → A
  | MySum.inl e => emptyElim e
  | MySum.inr a => a


/-
Map from A to Empty + A.
-/

def aToEmptySum {A : Type} : A → MySum MyEmpty A :=
  fun a => MySum.inr a


example {A : Type} (a : A) :
    emptySumToA (aToEmptySum a) = a := by
  rfl


/-
Logical versions.
-/

def orFalseToP {P : Prop} : MyOr P MyFalse → P
  | MyOr.inl p => p
  | MyOr.inr hfalse => falseElim hfalse

def pToOrFalse {P : Prop} : P → MyOr P MyFalse :=
  fun p => MyOr.inl p

def falseOrToP {P : Prop} : MyOr MyFalse P → P
  | MyOr.inl hfalse => falseElim hfalse
  | MyOr.inr p => p

def pToFalseOr {P : Prop} : P → MyOr MyFalse P :=
  fun p => MyOr.inr p


/- 10. Built-in Sum and Or

Lean already has sum types and logical OR.

Built-in sum type:
    Sum A B

Constructors:
    Sum.inl : A → Sum A B
    Sum.inr : B → Sum A B

Built-in logical OR:
    Or P Q

Notation:
    P ∨ Q

Constructors:
    Or.inl : P → P ∨ Q
    Or.inr : Q → P ∨ Q
-/

#check Sum
-- Sum : Type u → Type v → Type (max u v)

#check Sum.inl
#check Sum.inr

#check Or
-- Or : Prop → Prop → Prop

#check Or.inl
#check Or.inr

#check (2 = 2 ∨ 3 = 4)
-- 2 = 2 ∨ 3 = 4 : Prop


example : 2 = 2 ∨ 3 = 4 :=
  Or.inl rfl

example : 2 = 3 ∨ 4 = 4 :=
  Or.inr rfl


/-
Eliminating built-in Or can be done by pattern matching.
-/

example {P Q R : Prop} (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R :=
  match h with
  | Or.inl p => hp p
  | Or.inr q => hq q


/-
Or by the `cases` tactic.
-/

example {P Q : Prop} (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl p =>
      exact Or.inr p
  | inr q =>
      exact Or.inl q


/-
Summary table

Type theory                         Logic

MySum A B : Type                    MyOr P Q : Prop

MySum.inl a : MySum A B             MyOr.inl p : MyOr P Q
MySum.inr b : MySum A B             MyOr.inr q : MyOr P Q

Data is either from A or from B.     Proof is either of P or of Q.

To define MySum A B → C,            To prove MyOr P Q → R,
give both:                          give both:

    A → C                               P → R
    B → C                               Q → R

Universal property:

    (A + B → C)                     ((P ∨ Q) → R)
        ≃                               ↔
    (A → C) × (B → C)               (P → R) ∧ (Q → R)

Empty type corresponds to False.

    A + Empty ≅ A                  P ∨ False ↔ P
    Empty + A ≅ A                  False ∨ P ↔ P

Category theory:

    Sum type = coproduct
    Empty type = initial object
    Or = coproduct in logic/propositions
-/
