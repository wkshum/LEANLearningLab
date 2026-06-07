/-
 No import from Mathlib
-/

namespace LectureUnit

/- 1. Defining our own Unit type

The unit type is a type with exactly one element.

Lean already has a built-in type called `Unit`, so we define our
own version inside a namespace to avoid confusion.

The type `MyUnit` has one constructor:

    MyUnit.star : MyUnit

So there is exactly one canonical term of type `MyUnit`.
-/

inductive MyUnit : Type where
  | star : MyUnit

#check MyUnit
-- MyUnit : Type

#check MyUnit.star
-- MyUnit.star : MyUnit


/-
We can define an element of MyUnit.
-/

def u0 : MyUnit :=
  MyUnit.star

#check u0
-- u0 : MyUnit


/- 2. Elimination principle for MyUnit


To define a function out of MyUnit, it is enough to say what
the function does to the single element `MyUnit.star`.

For example, a function MyUnit → Nat is determined by the value
assigned to `MyUnit.star`.
-/

def unitToNat : MyUnit → Nat
  | MyUnit.star => 37

#eval unitToNat MyUnit.star
-- 37


def unitToBool : MyUnit → Bool
  | MyUnit.star => true

#eval unitToBool MyUnit.star
-- true


/-
General eliminator for MyUnit.

Given:
    C : Type
    c : C

we can define a function:

    MyUnit → C

by sending the unique element of MyUnit to c.
-/

def unitElim {C : Type} (c : C) : MyUnit → C
  | MyUnit.star => c

#eval unitElim 100 MyUnit.star
-- 100

#eval unitElim false MyUnit.star
-- false


/-
Computation rule:

    unitElim c MyUnit.star = c

This is true by computation, so `rfl` proves it.
-/

example {C : Type} (c : C) :
    unitElim c MyUnit.star = c := by
  rfl


/- 3. Every element of MyUnit is equal to star


Since MyUnit has only one constructor, every element of MyUnit
must be `MyUnit.star`.

This is the eta principle for Unit.
-/

theorem unitEta (u : MyUnit) :
    u = MyUnit.star := by
  cases u
  rfl


theorem all_units_equal (u v : MyUnit) :
    u = v := by
  cases u
  cases v
  rfl


/- 4. MyUnit as terminal object

In category theory, Unit is the terminal object in the category of types.

This means:

    For every type A, there is exactly one function A → MyUnit.

The unique function sends every input to MyUnit.star.
-/

def toUnit {A : Type} : A → MyUnit :=
  fun _a => MyUnit.star

#check toUnit
-- toUnit : A → MyUnit


/-
Example:
-/

#eval toUnit 5
-- MyUnit.star


/-
Any function A → MyUnit is equal to this one.

This uses function extensionality, because we prove equality of functions
by proving they agree on every input.
-/

theorem toUnit_unique {A : Type} (f : A → MyUnit) :
    f = toUnit := by
  funext a
  apply unitEta


/-  5. Unit in Lean

Lean already has a built-in unit type:

    Unit : Type

Its unique element is:

    () : Unit

or equivalently:

    Unit.unit : Unit
-/

#check Unit
-- Unit : Type

#check ()
-- () : Unit

#check Unit.unit
-- Unit.unit : Unit


def builtInUnitExample : Unit :=
  ()

#check builtInUnitExample
-- builtInUnitExample : Unit


/-
A function into Lean's built-in Unit is also unique.
-/

def toBuiltInUnit {A : Type} : A → Unit :=
  fun _a => ()

theorem toBuiltInUnit_unique {A : Type} (f : A → Unit) :
    f = toBuiltInUnit := by
  funext a
  cases f a
  rfl


/- 6. Unit and product types

Unit behaves like a neutral element for product.

Mathematically:

    A × Unit ≅ A
    Unit × A ≅ A

We define our own product type as a structure.
-/

structure Prod (A B : Type) where
  fst : A
  snd : B


/-
Map from A × Unit to A.
-/

def prodUnitToA {A : Type} : Prod A MyUnit → A :=
  fun p => p.fst


/-
Map from A to A × Unit.
-/

def aToProdUnit {A : Type} : A → Prod A MyUnit :=
  fun a => Prod.mk a MyUnit.star


/-
Computation:
-/

example {A : Type} (a : A) :
    prodUnitToA (aToProdUnit a) = a := by
  rfl


/-
The other direction:
-/

example {A : Type} (p : Prod A MyUnit) :
    aToProdUnit (prodUnitToA p) = p := by
  cases p with
  | mk a u =>
      cases u
      rfl


/-
Similarly, Unit × A ≅ A.
-/

def unitProdToA {A : Type} : Prod MyUnit A → A :=
  fun p => p.snd

def aToUnitProd {A : Type} : A → Prod MyUnit A :=
  fun a => Prod.mk MyUnit.star a

example {A : Type} (a : A) :
    unitProdToA (aToUnitProd a) = a := by
  rfl

example {A : Type} (p : Prod MyUnit A) :
    aToUnitProd (unitProdToA p) = p := by
  cases p with
  | mk u a =>
      cases u
      rfl


/-
So MyUnit is the identity object for product types.
-/


/- 7. Logical analogue: True

Under Curry--Howard:

    Unit corresponds to True.

`Unit` is a type with one element.

`True` is a proposition with one obvious proof.

Lean already has:

    True : Prop

and its proof is:

    True.intro : True
-/

#check True
-- True : Prop

#check True.intro
-- True.intro : True


/-
We can define our own version of True.
-/

inductive MyTrue : Prop where
  | intro : MyTrue

#check MyTrue
-- MyTrue : Prop

#check MyTrue.intro
-- MyTrue.intro : MyTrue


/-
To prove MyTrue, use its constructor.
-/

example : MyTrue :=
  MyTrue.intro

example : True :=
  True.intro


/- 8. Eliminating True

A proof of True contains no useful information. It is always trivial.

From True alone, we cannot prove an arbitrary proposition P.
But if we already have a proof p : P, then True → P.
-/

example {P : Prop} (p : P) : True → P :=
  fun _hTrue => p

example {P : Prop} (p : P) : MyTrue → P :=
  fun _hTrue => p


/-
Every proposition implies True.
-/

example {P : Prop} : P → True :=
  fun _p => True.intro

example {P : Prop} : P → MyTrue :=
  fun _p => MyTrue.intro


/-
This is the logical version of:

    for every type A, there is a function A → Unit.

Compare:

    A → Unit       terminal object property
    P → True      logical truth is always provable from any assumption
-/


/- 9. True and conjunction


True is the identity for conjunction:

    P ∧ True  ↔ P
    True ∧ P  ↔ P

We define our own And as a structure.
-/

structure And (P Q : Prop) : Prop where
  fst : P
  snd : Q


/-
P ∧ True → P
-/

def andTrueToP {P : Prop} : And P True → P :=
  fun h => h.fst


/-
P → P ∧ True
-/

def pToAndTrue {P : Prop} : P → And P True :=
  fun p => And.mk p True.intro


/-
True ∧ P → P
-/

def trueAndToP {P : Prop} : And True P → P :=
  fun h => h.snd


/-
P → True ∧ P
-/

def pToTrueAnd {P : Prop} : P → And True P :=
  fun p => And.mk True.intro p


/-
Examples:
-/

example {P : Prop} : And P True → P :=
  andTrueToP

example {P : Prop} : P → And P True :=
  pToAndTrue

example {P : Prop} : And True P → P :=
  trueAndToP

example {P : Prop} : P → And True P :=
  pToTrueAnd


/- Summary table

Type theory                 Logic                   Category theory

MyUnit : Type               MyTrue : Prop           terminal object
MyUnit.star : MyUnit        MyTrue.intro : MyTrue   unique/trivial proof

A → MyUnit                  P → True                unique map to terminal object
Prod A MyUnit ≅ A           And P True ↔ P          product identity law
Prod MyUnit A ≅ A           And True P ↔ P          product identity law

In words:

- Unit is the type with exactly one element.
- True is the proposition with a trivial proof.
- Unit is the terminal object in the category of types.
- True is the terminal object in the logic of propositions.
- Product with Unit changes nothing.
- Conjunction with True changes nothing.
-/

end LectureUnit
