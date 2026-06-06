/-
  Need not import any library from Mathlib
-/

/-
  Curry-Howard correspondence between Product and And
-/



section Product_and_And

-- since Lean already have the definition of
-- Prod and And, we use a namespace
-- to create an isolated programming environment

#check Prod  -- already defined in Lean
#check And  -- already defined in Lean

namespace prod

/-
Product type as a structure.

An element of `Prod A B` contains:
- `fst : A`
- `snd : B`
-/
structure Prod (A B : Type) where
  fst : A
  snd : B

#check Prod.mk
-- Prod.mk : {A B : Type} → A → B → Prod A B

variable {A B : Type}
variable (a : A) (b : B)

#check Prod.mk a b
-- Prod.mk a b : Prod A B


/-
Logical conjunction as a structure.

A proof of `And P Q` contains:
- `fst : P`, a proof of P
- `snd : Q`, a proof of Q
-/
structure And (P Q : Prop) : Prop where
  fst : P
  snd : Q

#check And.mk
-- And.mk : {P Q : Prop} → P → Q → And P Q

-- Construction

def p0 : Prod Nat Bool :=
  Prod.mk 3 true

def p1 : Prod String Nat :=
  Prod.mk "hello" 5

example : And (2 = 2) (1 = 1) :=
  And.mk rfl rfl

-- Since these are structures, we can use field notation:

def p0' : Prod Nat Bool :=
  { fst := 3, snd := true }

def p1' : Prod String Nat :=
  { fst := "hello", snd := 5 }

example : And (2 = 2) (1 = 1) :=
  {fst := rfl, snd := rfl}


-- Elimination / Projection for Pord
-- For a structure, Lean automatically gives projections:
-- Prod.fst : Prod A B → A
-- Prod.snd : Prod A B → B

def first_part_of {A B : Type} : Prod A B → A :=
  Prod.fst

def second_part_of {A B : Type} : Prod A B → B :=
  Prod.snd

#eval first_part_of p0  -- 3

#eval second_part_of p0  -- true

example {A B : Type} (a : A) (b : B) :
    first_part_of (Prod.mk a b) = a := by
  rfl

example {A B : Type} (a : A) (b : B) :
    second_part_of (Prod.mk a b) = b := by
  rfl

-- dot notation in Lean

#eval p0.fst  -- 3

#eval p0.snd  -- true


-- Elimination / projection for And
-- Lean automatically creates two projections: fst and snd
-- And.fst : And P Q → P
-- And.snd : And P Q → Q

example (h : And (2 = 2) (3 = 3)) : 2 = 2 :=
  And.fst h

example (h : And (2 = 2) (3 = 3)) : 3 = 3 :=
  And.snd h

-- Computation rule for And

example {P Q : Prop} (p : P) (q : Q) :
    And.fst (And.mk p q) = p := by
  rfl

example {P Q : Prop} (p : P) (q : Q) :
    And.snd (And.mk p q) = q := by
  rfl

-- Convenient notation: define left and right
def left {P Q : Prop} : And P Q → P :=
  And.fst

def right {P Q : Prop} : And P Q → Q :=
  And.snd

example {P Q : Prop} (p : P) (q : Q) :
    left (And.mk p q) = p := by
  rfl

example {P Q : Prop} (p : P) (q : Q) :
    right (And.mk p q) = q := by
  rfl

-- Swapping components

def swap {A B : Type} : Prod A B → Prod B A :=
  fun p => Prod.mk p.snd p.fst

example : swap (Prod.mk 3 true) = Prod.mk true 3 := by
  rfl

-- equivalently, with pattern matching
def swap' {A B : Type} : Prod A B → Prod B A
  | Prod.mk a b => Prod.mk b a

example : swap' (Prod.mk 3 true) = Prod.mk true 3 := by
  rfl

-- For conjunction, we know that `and` is commutative
--
def andComm {P Q : Prop} : And P Q → And Q P :=
  fun h => And.mk h.snd h.fst

-- definition of addComm' using left and right
def andComm' {P Q : Prop} : And P Q → And Q P :=
  fun h => And.mk (right h) (left h)


-- Curry and uncurry for Prod
def curry {A B C : Type} :
    (Prod A B → C) → A → B → C :=
  fun f a b => f (Prod.mk a b)

def uncurry {A B C : Type} :
    (A → B → C) → Prod A B → C :=
  fun f p => f p.fst p.snd

def addCurried : Nat → Nat → Nat :=
  fun a b => a + b

#eval uncurry addCurried (Prod.mk 10 20) -- 30

-- computation rule
example {A B C : Type} (f : A → B → C) (a : A) (b : B) :
    uncurry f (Prod.mk a b) = f a b := by
  rfl

-- Curry and uncurry for And
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


-- eta rule for Prod
theorem prodEta {A B : Type} (p : Prod A B) :
    p = Prod.mk (Prod.fst p) (Prod.snd p) := by
  cases p with
  | mk a b =>
      rfl

-- alternately, we can also write
theorem prodEta' {A B : Type} (p : Prod A B) :
    p = { fst := p.fst, snd := p.snd } := by
  cases p
  rfl

-- eta rule for And
theorem andEta {P Q : Prop} (h : And P Q) :
    h = And.mk (left h) (right h) := by
  cases h with
  | mk p q =>
      rfl

-- or with field notation
theorem andEta' {P Q : Prop} (h : And P Q) :
    h = { fst := h.fst, snd := h.snd } := by
  cases h
  rfl


-- pair map for Prod
def pairMap {X A B : Type}
    (f : X → A) (g : X → B) :
    X → Prod A B :=
  fun x => Prod.mk (f x) (g x)

example {X A B : Type} (f : X → A) (g : X → B) (x : X) :
    (pairMap f g x).fst = f x := by
  rfl

example {X A B : Type} (f : X → A) (g : X → B) (x : X) :
    (pairMap f g x).snd = g x := by
  rfl


-- pair map for conjunction
def andPairMap {R P Q : Prop}
    (f : R → P) (g : R → Q) :
    R → And P Q :=
  fun r => And.mk (f r) (g r)

example {R P Q : Prop}
    (f : R → P) (g : R → Q) (r : R) :
    left (andPairMap f g r) = f r := by
  rfl

example {R P Q : Prop}
    (f : R → P) (g : R → Q) (r : R) :
    right (andPairMap f g r) = g r := by
  rfl



-- some type checking
#check Prod Nat Bool
-- Prod Nat Bool : Type

#check Prod.mk 37 true
-- Prod.mk 37 true : Prod Nat Bool

#check And (2 = 2) (3 = 3)
-- And (2 = 2) (3 = 3) : Prop

def test : And (2 = 2) (3 = 3) :=
  And.mk rfl rfl

#check test
-- test : And (2 = 2) (3 = 3)



/- Summary table

Product in type theory        And in logic
Prod A B : Type	              And P Q : Prop
Prod.mk a b : Prod A B	      And.mk p q : And P Q
Prod.fst : Prod A B → A	      And.fst : And P Q → P
Prod.snd : Prod A B → B	      And.snd : And P Q → Q

To construct Prod A B,        To prove And P Q,
give a : A and b : B.	        provide p : P and q : Q.

To use x : Prod A B,          To use h : And P Q,
extract x.fst and x.snd       extract h.fst and h.snd.


Conclusion: Logical conjunction is the product operation
in the world of propositions.
-/


end prod

end Product_and_And
