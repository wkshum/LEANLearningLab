/-

  Lean Learning Lab
  19 Nov 2025

  Examples of types in LEAN4

-/

import Mathlib.Tactic



namespace inductive_type

-- polymorphic list type
inductive MyList (A : Type) : Type 
| nil : MyList A  -- empty list
| cons (head : A) (tail : MyList A) : MyList A

open MyList

-- construct an empty using the constructor `nil`
def emptyList : MyList Nat := nil

-- -- list [1,2,3]
def List123 : MyList Nat := 
cons 1 (cons 2 (cons 3 nil))

-- concatentation of two lists
def append {A : Type} (L1 L2 : MyList A) : MyList A :=
  match L1 with
  | nil  => L2
  | cons h tail => cons h (append tail L2)

-- compute the length of a list recursively
def length {A : Type} (L : MyList A) := 
  match L with 
  | nil  => 0
  | cons _ tail => 1 + length tail

#eval length List123    -- 3
#eval length (append List123 List123)    -- 6

end inductive_type



namespace equality_type

-- Define the natural number type
inductive MyNat : Type where
  | zero : MyNat 
  | succ (n : MyNat) : MyNat 

-- addition of two natural numbers
def add (a b : MyNat) : MyNat :=
  match a with
  | MyNat.zero => b   -- 0 + b is defined as b
  | MyNat.succ n => MyNat.succ (add n b) 
  -- (n+1)+b is defined as (n+b)+1

open MyNat 

-- the first three natural numbers
def one := succ zero
def two := succ one
def three := succ two 

-- prove that 3=3
theorem three_equals_three : three = three := rfl

-- another proof of 3=3
theorem three_equals_three1 : Eq three three := Eq.refl three 

-- 1+1=2
theorem OnePlusOneEqualTwo : add one one = two := by rfl 

-- type of `three_equals_three` is a term of type `three = three`
#check three_equals_three  -- three = three

-- prove if x = y, then z+x = z+y
theorem add_is_consistent (x y z : MyNat)
  (h : x = y) : add z x = add z y := by 
    rewrite [h]
    rfl 

-- another proof of the previous theorem
theorem add_is_consistent' (x y z : MyNat)
  (h : x = y) : add z x = add z y := by 
    rw [h]

-- `add_is_consistent` is a proof term
#check add_is_consistent   -- add z x = add z y

-- equality type
#print Eq 


-- -- a simplified definition of the Equality type 
inductive Eq {A : Type} (a : A) : A → Prop where
  | refl : Eq a a

-- /-
-- `Eq` is an inductive type
-- `(a : A)` in the definition indicates that `Eq` is an dependent type
-- The type `Eq a` is indexed by the term `a`.

-- `A → Prop` means that `Eq` has function type

-- `Eq` has only one constructor refl

-- -/

end equality_type



namespace pi_type

-- -- Vector is a list with a given length
inductive Vector (A : Type) : Nat → Type where
  | nil : Vector A 0 
  | cons {n : Nat} (head : A) (tail : Vector A n) 
     : Vector A (n + 1) 

open Vector 

-- check the type of Vector
#check Vector  -- pi_type.Vector (A : Type) : ℕ → Type

-- -- nil vector
def vec_nil : Vector Nat 0 := nil

-- -- vector of dimension 1
def vec_1 : Vector Nat 1 := cons 42 nil

#print vec_1

-- -- vector of dimension 3
def vec_dim_3 : Vector Nat 3 := 
  cons 10 ( cons 334 ( cons 223413 nil))

-- type of vec_dim_3
#check vec_dim_3   -- pi_type.vec_dim_3 : Vector ℕ 3

-- -- define a vector with constant component
def replicate {A : Type} (n : Nat) (a : A) : Vector A n :=
  match n with
  | 0  => nil
  | n+1 => cons a (replicate n a)

--   [true, true, true, true, true]
def v5 := replicate 5 true 

#eval v5 

-- ["a", "a", "a"]
def v3 := replicate 3 "a" 
#check v3   -- pi_type.v3 : Vector String 3


end pi_type 


namespace subtype

-- -- subtype in LEAN is an example of sigma type
-- -- notation: `{ x : T // P x }`
-- -- This means "the type of all x's of type T 
-- --     such that the property P x is true".

-- a custom type of small natural number
def SmallNat := {n : Nat // n < 10}

-- -- To define an object, we provide the value 6 
-- -- and a proof that 6 < 10.
def six : SmallNat := ⟨ 6, by simp ⟩ 

def eight : SmallNat := ⟨8, by simp⟩ 

#check eight
#print eight 

-- add the values of two SmallNat
def addSmallNat (a b : SmallNat) : Nat :=
  a.val + b.val 


#eval addSmallNat six eight   -- 14


-- -- a subtype of even numbers
-- -- an element consists of a natural number and a proof
-- -- that it is even

-- Definition of evenness
inductive IsEven : Nat → Prop where 
  | even_zero : IsEven 0
  | even_succ_succ {n : Nat} (h: IsEven n) : IsEven (n+2)

-- proof that 4 is even
def four_is_even : IsEven 4 := 
  IsEven.even_succ_succ 
  (IsEven.even_succ_succ IsEven.even_zero) 

#check four_is_even 

-- Define a Sigma-type EvenNat
def EvenNat := {n: Nat // IsEven n}

-- create an element of EvenNat
def four_even : EvenNat := ⟨4, four_is_even⟩

#check four_even   -- subtype.four_even : EvenNat
#print four_even 
-- def subtype.four_even : EvenNat :=
-- ⟨4, four_is_even⟩

#check four_even.val   -- the value of four_even
#check four_even.property   -- the property of four_even

-- 6 as an element of EvenNat
def six_even : EvenNat :=
  ⟨6, IsEven.even_succ_succ four_is_even⟩ 

#check six_even  -- subtype.six_even : EvenNat

-- -- impossible construction
-- def three_even : EvenNat := ⟨3, sorry ⟩ 

-- #check three_even 

-- -- a function that safely return half of an even number
def half (e : EvenNat) : Nat := 
  e.val / 2

#eval half four_even -- 2
#eval half six_even   -- 3

-- def EvenNat := {n: Nat // IsEven n}
def EvenNat' := Subtype (fun n => IsEven n)

end subtype

-- /-
-- A rule in LEAN programming:
-- `Subtype` is for bundling data with a proof (Prop).
-- `Sigma` is for bundling data with other data (Type).
-- -/



namespace sigma_type

-- -- Define a type that can hold a value of any type.
-- -- The first element of the pair is a Type itself, e.g. Nat
-- -- The second element of the pair is a value the specified type
def AnyValue := Σ (T: Type) , T 

-- -- Example: a pair of type Nat and value 10
def nat_val : AnyValue := ⟨Nat, 5⟩ 

#check nat_val 

-- -- Example: a pair of type Bool and value true
def bool_val : AnyValue := ⟨Bool, true⟩ 

-- -- Incorrect construction
-- def wrong_example : AnyValue := ⟨Bool, 3⟩ 

-- -- Example a pair of type String and value "HELLO"
def string_val : AnyValue := ⟨String , "HELLO"⟩ 

#print string_val

def getType (v : AnyValue) := v.1 
def getValue (v : AnyValue) := v.2 

#check getType nat_val 
-- #eval getType nat_val  -- wrong

#eval getValue nat_val 


/-
Summary: 

*Inductive Types*: How to define your own data and logic 
  (`MyNat`, `MyList`, `IsEven`).

*Equality Type* : How to prove things are equal 
  (rfl, rewrite).

*Π-types* (Dependent Functions): Functions where the return type depends on the input value.

*Σ-types* (Dependent Pairs): Data structures where the type of one part 
  depends on the value of another.

-/
end sigma_type
