/-
  No import from Mathlib
-/

namespace Function_and_implication

/-
Function type and logical implication

Given two types A and B
a function A → B transforms data of type A into data of type B

Given two propositions P and Q
a proof P → Q transforms a proof of P into a proof of Q

-/


/-  1. Function types at the level of data

If A and B are types, then
    A → B
is the type of functions from A to B.

To construct a term of type A → B, we write a lambda expression:
    fun x : A => ...

To use a function f : A → B, we apply it to an input a : A:
    f a : B
-/

-- A simple function from Nat to Nat
def addOne : Nat → Nat :=
  fun n => n + 1

#check addOne   -- addOne : Nat → Nat

#eval addOne 5  -- 6


-- A function from Bool to Nat
def boolToNat : Bool → Nat :=
  fun b =>
    match b with
    | true => 1
    | false => 0

#eval boolToNat true  -- 1

#eval boolToNat false  -- 0


/-  2. Construction and elimination for function types

Construction rule:

    If assuming x : A, we can construct something of type B,
    then we get a function A → B.

In Lean, we write it as

    fun x : A => ...

Elimination rule:

    If f : A → B and a : A,
    then f a : B.

This is function application.
-/

-- Construction
-- A constant function
def constNat : Bool → Nat :=
  fun _b => 16

#eval constNat true    -- 16

#eval constNat false   -- 16


-- Elimination / application
def applyFunction {A B : Type} (f : A → B) (a : A) : B :=
  f a

#eval applyFunction addOne 10  -- 11

#eval applyFunction addOne (constNat true)   -- 17



/- 3. Computation rule

The basic computation rule for functions is (using notation from lambda calculus)

    (fun x => t) a = t[a/x]

In the term t, replace all the occurence of x by a.
Computation for function is substitution.
This is also called beta reduction.

In Lean, this is usually proved by rfl.
-/

example : (fun n : Nat => n + 1) 5 = 6 := by
  rfl

example {A B : Type} (a : A) (b : B) :
    (fun _x : A => b) a = b := by
  rfl

example (n : Nat) :
    (fun x : Nat => x + 1) n = n + 1 := by
  rfl


/-  4. Logical implication

Now move from Type to Prop.

If P and Q are propositions, then

    P → Q

means logical implication:

    if P, then Q.

A proof of P → Q is a function which transforms
a proof of P into a proof of Q.
-/


-- Example: P implies P
def impRefl {P : Prop} : P → P :=
  fun p => p

example {P : Prop} : P → P :=
  fun p => p


-- Example: from P and P → Q, prove Q.
-- This is modus ponens.
def modusPonens {P Q : Prop} : (P → Q) → P → Q :=
  fun h p => h p

example {P Q : Prop} (h : P → Q) (p : P) : Q :=
  h p

/- 5. Construction and elimination for implication


Construction rule for implication:

    To prove P → Q,
    assume p : P and prove Q.

Elimination rule for implication:

    From h : P → Q and p : P,
    get h p : Q.

This is exactly the same as function construction/application.
-/

-- Construction of an implication proof
example {P Q : Prop} (q : Q) : P → Q :=
  fun _p => q

-- Elimination of implication
example {P Q : Prop} (h : P → Q) (p : P) : Q :=
  h p



/-   6. Transitivity of implication

If P implies Q and Q implies R, then P implies R.

This is function composition at the level of proofs.
-/

def impTrans {P Q R : Prop} :
    (P → Q) → (Q → R) → (P → R) :=
  fun hpq hqr =>
    fun p =>
      hqr (hpq p)

example {P Q R : Prop}
    (hpq : P → Q)
    (hqr : Q → R) :
    P → R :=
  fun p => hqr (hpq p)


/-
At the data level, this is ordinary function composition.
-/

def comp {A B C : Type} :
    (A → B) → (B → C) → (A → C) :=
  fun f g =>
    fun a =>
      g (f a)

#eval comp addOne addOne 10   -- 12



/- 7. Identity function and identity implication
-/

def idData {A : Type} : A → A :=
  fun a => a

def idProof {P : Prop} : P → P :=
  fun p => p

example : idData 5 = 5 := by
  rfl

example {P : Prop} : P → P :=
  idProof



/- 8. Constant functions and weakening in logic

At the data level:

    A → B → A

takes an A and a B and returns the A.

At the logic level:

    P → Q → P

means:

    if P is true, then Q implies P.

This is one of the basic tautologies.
-/


def constData {A B : Type} : A → B → A :=
  fun a _b => a

#eval constData 10 true
-- 10

example {P Q : Prop} : P → Q → P :=
  fun p _q => p


/- 9. Curry and uncurry for product type

Recall the product type:

    Prod A B

represents A × B.

A function from A to B to C:

    A → B → C

is a curried function.

A function from Prod A B to C:

    Prod A B → C

is an uncurried function.

These are equivalent.
-/

structure Prod (A B : Type) where
  fst : A
  snd : B

def curry {A B C : Type} :
    (Prod A B → C) → A → B → C :=
  fun f a b => f (Prod.mk a b)

def uncurry {A B C : Type} :
    (A → B → C) → Prod A B → C :=
  fun f p => f p.fst p.snd

def addCurried : Nat → Nat → Nat :=
  fun a b => a + b

def addUncurried : Prod Nat Nat → Nat :=
  uncurry addCurried

#eval addCurried 3 4
-- 7

#eval addUncurried (Prod.mk 3 4)  -- 7

#eval uncurry addCurried (Prod.mk 10 20) -- 30

-- computation rule
example {A B C : Type} (f : A → B → C) (a : A) (b : B) :
    uncurry f (Prod.mk a b) = f a b := by
  rfl

example {A B C : Type} (f : Prod A B → C) (a : A) (b : B) :
    curry f a b = f (Prod.mk a b) := by
  rfl


/- 10. Logical version: implication and conjunction

For propositions, the analogous fact is:

    (P ∧ Q → R) is equivalent to (P → Q → R)

We define our own And as a structure.
-/

structure And (P Q : Prop) : Prop where
  fst : P
  snd : Q

def andCurry {P Q R : Prop} :
    (And P Q → R) → P → Q → R :=
  fun f p q => f (And.mk p q)

def andUncurry {P Q R : Prop} :
    (P → Q → R) → And P Q → R :=
  fun f h => f h.fst h.snd

example {P Q R : Prop}
    (h : And P Q → R) :
    P → Q → R :=
  andCurry h

example {P Q R : Prop}
    (h : P → Q → R) :
    And P Q → R :=
  andUncurry h

-- Computation rule
example {P Q R : Prop} (f : P → Q → R) (p : P) (q : Q) :
    andUncurry f (And.mk p q) = f p q := by
  rfl



/- 11. Function extensionality: eta rule

    f = fun x => f x

Mathematically, two functions are equal if they give equal outputs
on every input.

In Lean, this uses function extensionality.
-/

-- Given a function f,
-- f is equal to the function defined by f x
example {A B : Type} (f : A → B) :
    f = (fun x => f x) := by
  rfl

-- two functions f and g are equal if
-- f x = g x for all input x
example {A B : Type} (f g : A → B)
    (h : ∀ x : A, f x = g x) :
    f = g := by
  funext x
  exact h x


/-   12. Summary


Type theory                  Logic

A : Type                     a type of data
B : Type                     another type of data
P : Prop                     a proposition
Q : Prop                     another proposition

a : A                        a datum of type A
p : P                        a proof of proposition P

A → B                        function type
P → Q                        implication

fun a : A => ...             construct a function
fun p : P => ...             prove an implication

f a : B                      apply a function to data
h p : Q                      modus ponens

A → B → C                    curried function of two inputs
P → Q → R                    nested implication

Prod A B → C                 function from a pair
And P Q → R                  proof using a conjunction

(A → B) → (B → C) → A → C    function composition
(P → Q) → (Q → R) → P → R    transitivity of implication
-/


end Function_and_implication
