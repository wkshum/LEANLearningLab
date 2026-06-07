namespace LectureDependentProduct

/- 1. The Dependent Function Type (Pi type)

A normal function `A → B` has a fixed return type. No matter what
input you give it, the output is always of type `B`.

A dependent function allows the RETURN TYPE to depend on the VALUE
of the input.

If
    A : Type
    B : A → Type    (A family of types indexed by A)

then
    (a : A) → B a   : Type

is the type of dependent functions. An element is a function `f` where:
    - it takes an input `a : A`
    - it returns a value of type `B a`.

Because this is a core primitive of Lean, we cannot define it as an
`inductive` type. Instead, we create a shorthand `def` alias.
-/

def MyPi (A : Type) (B : A → Type) : Type :=
  (a : A) → B a

#check MyPi   -- MyPi : (A : Type) → (A → Type) → Type


/- 2. Constructing elements of a dependent function type

Let's reuse our `MyFamily` type from the dependent sum example.
If the input is `true`, the return type is `Nat`.
If the input is `false`, the return type is `String`.
-/

def MyFamily (b : Bool) : Type :=
  match b with
  | true  => Nat
  | false => String

/-
To construct a dependent function, we use standard function
syntax (pattern matching or `fun` / lambda abstraction).

Notice how the compiler checks that the return values match
the specific type required by each branch!
-/

def myDepFun : MyPi Bool MyFamily
  | true  => (42:Nat)        -- Must be Nat because MyFamily true = Nat
  | false => "hello"   -- Must be String because MyFamily false = String

#check myDepFun    -- myDepFun : MyPi Bool MyFamily


/- 3. Eliminating (Using) a dependent function

To use a dependent function, you simply apply it to an argument.
The magic of dependent types is that Lean computes the type of the
result based on the argument you provide!
-/

-- If we apply it to `true`, Lean knows the result is a `Nat`.
#check myDepFun true
-- myDepFun true : MyFamily true  (which is definitionally Nat)

#eval myDepFun true
-- 42

-- If we apply it to `false`, Lean knows the result is a `String`.
#check myDepFun false
-- myDepFun false : MyFamily false (which is definitionally String)

#eval myDepFun false
-- "hello"


/- 4. Connection to regular function types

If the type family `B` actually ignores its input (i.e., it is a
constant family), the dependent function type reduces to a regular
function type `A → B`.
-/

def ConstantFamily (A B : Type) (_a : A) : Type := B



/- 5. Logical analogue: Universal Quantifier (Forall / ∀)

Under Curry-Howard:
    Dependent function type (Pi) corresponds to the Universal Quantifier (∀).

At the type level:
    (a : A) → B a
means "a function that gives you data `B a` for any input `a`".

At the proposition level:
    ∀ (a : A), P a
means "a proof that `P a` holds for any `a`".

In Lean, the universal quantifier `∀` and the dependent function `→`
are literally the EXACT SAME core expression. They are just written
differently for human readability!
-/

def MyForall {A : Type} (P : A → Prop) : Prop :=
  (a : A) → P a

#check MyForall
-- MyForall : {A : Type} → (A → Prop) → Prop


/-
Examples of proving a Forall.
We want to prove: "For all natural numbers n, n = n"
We prove this by writing a FUNCTION that takes an arbitrary `n`,
and returns a proof of `n = n`.
-/

def proofForAllN : MyForall (fun (n : Nat) => n = n) :=
  fun _n => rfl

/-
To use (eliminate) a Forall proof, we apply it to a specific value,
exactly like applying a function!
-/

#check proofForAllN 5   -- proofForAllN 5 : 5 = 5

example : 5 = 5 := proofForAllN 5


/- 6. Built-in Pi and Forall syntax

Lean has built-in notation for dependent functions and universal quantifiers.

In older versions of Lean (and in other proof assistants like Agda or Coq),
Π (x : A), B x was the standard way to write a dependent function type.

In Lean 4, the Π (Pi) notation was intentionally removed
from the core language to simplify the syntax.
-/
#check (b : Bool) →  MyFamily b -- (b : Bool) → MyFamily b : Type

#check ∀ (n : Nat), n = n   -- ∀ (n : Nat), n = n : Prop


/-
Under the hood, `∀` is exactly the same as the dependent arrow.
Lean simply provides the `∀` symbol because it looks like traditional
first-order logic, making mathematical proofs easier to read.
-/


/-
Summary table

Type theory                         Logic

(a : A) → B a  : Type               ∀ a : A, P a  : Prop
(often written Π a : A, B a)

fun a => body                       fun a => proof
(where body : B a)                  (where proof : P a)

A function that returns data        A proof that works for
whose type depends on the input.    any arbitrary input.

To eliminate (use), apply it:       To eliminate (use), apply it:
    f x : B x                           h x : P x

Category theory / Set theory:

    Pi type = Cartesian product of a family of sets (Dependent Product).
    Forall = dependent product evaluated into propositional logic.
-/

end LectureDependentProduct
