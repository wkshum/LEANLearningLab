namespace LectureDependentSum

/- 1. Defining our own dependent sum type (Sigma type)

The dependent sum type generalizes the product type (pairs).

For a normal pair `Prod A B`, the type `B` is independent of `A`.
For a dependent sum, the type of the second element can depend
on the VALUE of the first element.

If
    A : Type
    B : A → Type    (This is a family of types indexed by A)

then
    MySigma A B : Type

is the type of dependent pairs. An element is a pair `(a, b)` where:
    - `a` is an element of `A`
    - `b` is an element of `B a` (the specific type depends on `a`)
-/

structure MySigma (A : Type) (B : A → Type) : Type where
  fst : A
  snd : B fst

#check MySigma   -- MySigma : (A : Type) → (A → Type) → Type

#check MySigma.mk
-- MySigma.mk : {A : Type} → {B : A → Type} → (fst : A) → B fst → MySigma A B


/- 2. Constructing elements of a dependent sum type

To show how the second type depends on the first value, let's define
a type family `MyFamily` over `Bool`.

If the boolean is `true`, the second element must be a `Nat`.
If the boolean is `false`, the second element must be a `String`.
-/

def MyFamily (b : Bool) : Type :=
  match b with
  | true  => Nat
  | false => String

-- Constructing pairs:
def sig0 : MySigma Bool MyFamily :=
  MySigma.mk true (42:Nat)  -- The second element is a Nat because the first is true

def sig1 : MySigma Bool MyFamily :=
  MySigma.mk false "hello"  -- The second element is a String because the first is false

#check sig0  -- sig0 : MySigma Bool MyFamily
#check sig1  -- sig1 : MySigma Bool MyFamily

/-
A term of type `MySigma A B` is always a pair:
    MySigma.mk a b
where `a : A` and `b : B a`.
-/


/- 3. Eliminating a dependent sum type

Because `MySigma` is a structure (a single-constructor record), we can
eliminate it by taking its projections: `.fst` and `.snd`.
Alternatively, we can use pattern matching to extract both pieces.
-/
def describeSigma : MySigma Bool MyFamily → String
  | MySigma.mk true (n : Nat) => "It's true, and the number is " ++ toString n
  | MySigma.mk false (s : String) => "It's false, and the string is " ++ s

#eval describeSigma sig0  -- "It's true, and the number is 42"
#eval describeSigma sig1  -- "It's false, and the string is hello"


/-
General eliminator for `MySigma`.

To map from `MySigma A B` to some type `C`, we must provide a function
that takes an `a : A` and a `b : B a`, and returns a `C`.
-/

def sigmaElim {A : Type} {B : A → Type} {C : Type}
    (f : (a : A) → B a → C) :
    MySigma A B → C
  | MySigma.mk a b => f a b




/- 4. Dependent Sum and Functions (Currying)

A function out of a dependent sum type

    MySigma A B → C

is equivalent to a curried function taking two arguments

    (a : A) → B a → C

Notice how this looks just like `A → B → C`, but the type of the second
argument `B a` depends on the value of the first argument `a`.
-/

def sigmaToCurried {A : Type} {B : A → Type} {C : Type} :
    (MySigma A B → C) → ((a : A) → B a → C) :=
  fun h a b => h (MySigma.mk a b)

def curriedToSigma {A : Type} {B : A → Type} {C : Type} :
    ((a : A) → B a → C) → (MySigma A B → C) :=
  fun f x =>
    match x with
    | MySigma.mk a b => f a b



/- 5. Logical analogue: Existential Quantifier (Exists / ∃)

Under Curry-Howard:
    Dependent sum type corresponds to the Existential Quantifier (∃).

At the type level:
    MySigma A B
means "give me an `a : A` and some data of type `B a`".

At the proposition level:
    MyExists A P
means "there exists some `a : A` such that `P a` is true".

To prove `∃ x, P x`, we must provide:
    - a witness `w : A`
    - a proof that `P w` holds.
-/

inductive MyExists {A : Type} (P : A → Prop) : Prop where
  | intro (w : A) (h : P w) : MyExists P

#check MyExists
-- MyExists : {A : Type} → (A → Prop) → Prop

#check MyExists.intro
-- MyExists.intro : {A : Type} → {P : A → Prop} → (w : A) → P w → MyExists P


/-
Examples of proving an existence.
We want to prove: "There exists a natural number n such that n = 5"
-/

example : MyExists (fun (n : Nat) => n = 5) :=
  MyExists.intro 5 rfl

example : MyExists (fun (n : Nat) => n + 2 = 7) :=
  MyExists.intro 5 rfl


/- 6. Eliminating Exists

To use a proof of `MyExists P`, we must be able to prove our goal `R`
regardless of which specific witness is used.

If we want to prove `R` from `MyExists P`, we need:
    For any `a : A`, if `P a` is true, then `R` is true.
    (∀ a, P a → R)

This is precisely "let `a` be an arbitrary element such that `P a` holds".
-/

def existsElim {A : Type} {P : A → Prop} {R : Prop}
    (h_exists : MyExists P)
    (h_forall : (a : A) → P a → R) :
    R :=
  match h_exists with
  | MyExists.intro w hw => h_forall w hw



/- 7. Exists and Implication

The logical eliminator above represents the equivalence:
    ((∃ x : A, P x) → R)  is equivalent to  (∀ x : A, P x → R)

This is the logical version of the Currying equivalence we saw in section 4.
-/

def existsToForall {A : Type} {P : A → Prop} {R : Prop} :
    (MyExists P → R) → ((a : A) → P a → R) :=
  fun h a hP => h (MyExists.intro a hP)

def forallToExists {A : Type} {P : A → Prop} {R : Prop} :
    ((a : A) → P a → R) → (MyExists P → R) :=
  fun f h_exists =>
    match h_exists with
    | MyExists.intro w hw => f w hw


/- 8. Sigma and Existsin Lean's programming

Lean has both of these built-in.

Built-in dependent sum:
    Sigma B    (often written as  Σ x : A, B x)

Constructor:
    Sigma.mk : (fst : A) → B fst → Sigma B

Built-in existential quantifier:
    Exists P   (often written as  ∃ x : A, P x)

Constructor:
    Exists.intro : (w : A) → P w → Exists P
-/

#check Sigma
-- Sigma : {A : Type u} → (A → Type v) → Type (max u v)

#check Exists
-- Exists : {A : Sort u} → (A → Prop) → Prop

-- Built-in notation examples:
#check Σ (n : Nat), Fin n
-- Σ (n : Nat), Fin n : Type

#check {n : Nat // n = 5}

#check ∃ (n : Nat), n = 5
-- ∃ (n : Nat), n = 5 : Prop

example : ∃ (n : Nat), n = 5 :=
  Exists.intro 5 rfl

-- You can also use the `⟨...⟩` anonymous constructor syntax:
example : ∃ (n : Nat), n + 2 = 7 :=
  ⟨5, rfl⟩

variable (A : Type) (B : A → Type)

-- Lean's built-in syntax:
#check Σ (a : A), B a
-- Σ (a : A), B a : Type

/-
The Type: MySigma A B becomes Σ (a : A), B a.

The Constructor (making a pair): MySigma.mk a b becomes
Sigma.mk a b, which is usually written using the anonymous bracket notation ⟨a, b⟩.

The Eliminators (extracting data): .fst and .snd become
exactly .fst and .snd on the built-in Sigma.
-/


/-
Summary table

Type theory                         Logic

MySigma A B : Type                  MyExists A P : Prop
(where B : A → Type)                (where P : A → Prop)

MySigma.mk a b                      MyExists.intro w h
(where b : B a)                     (where h : P w)

Data is a pair where the            Proof is a pair of a witness
type of the 2nd part depends        and a proof that the witness
on the value of the 1st part.       satisfies the predicate.

To define MySigma A B → C,          To prove MyExists A P → R,
give:                               give:
    (a : A) → B a → C                   (a : A) → P a → R

Universal property (Currying):
    (Σ x:A, B x) → C                (∃ x:A, P x) → R
        ≃                               ↔
    ∀ x:A, B x → C                  ∀ x:A, P x → R

Category theory / Set theory:

    Sigma type = coproduct of a family of types (Dependent Sum)
    Also represents = fibration / dependent pairs
    Exists = dependent sum evaluated into propositional logic
-/

end LectureDependentSum
