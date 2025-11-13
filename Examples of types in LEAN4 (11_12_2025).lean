/-

  Lean Learning Lab
  12 Nov 2025

  Examples of types in LEAN4

-/

import Mathlib.Tactic

namespace sum_type

-- def NatOrString := Nat ⊕ String 
def NatOrString := Sum Nat String 

#check NatOrString    -- sum_type.NatOrString : Type

-- a number
def n : NatOrString := Sum.inl 13   

-- a string
def s : NatOrString := Sum.inr "hello!"   

def process (x : NatOrString) : String := 
  match x with 
  | Sum.inl n => "A number " ++ toString n
  | Sum.inr s => "A string " ++ s

#eval process n  -- "A number 13"  
#eval process s  -- "A string hello!"

-- define binary tree
inductive Tree
| leaf : Nat → Tree
| node : Tree → Tree → Tree

def myTree : Tree := Tree.node (Tree.leaf 10) (Tree.leaf 22)  

#print myTree 

def sumTree : Tree → Nat 
| Tree.leaf n => n
| Tree.node left right => sumTree left + sumTree right

#eval sumTree myTree   -- 32

-- logical OR

example : 3=4 ∨ 3=3 := 
  Or.inr rfl 

end sum_type


namespace product_type

-- define product of Nat and String
-- def NatAndString := Nat × String
def NatAndString := Prod Nat String

-- construct a pair
def pair : NatAndString  := (13, "World") 

-- extract component
def first (p : NatAndString) : Nat := p.1
def second (p : NatAndString) : String := p.2

#eval first pair    -- 13
#eval second pair   -- "World"

-- pattern matching
def swap {A B : Type} (p : Prod A B) : Prod B A := 
  match p with
  | (a,b) => (b,a)

#eval swap (134,"hello")   -- ("hello", 134)

end product_type



namespace function_type

#check fun x => x+3   -- fun x ↦ x + 3 : ℕ → ℕ

#eval (fun x => x+3) 8     -- 11

-- multiply the input number by 3
def Triple : Nat → Nat := fun n => n*3

#eval Triple 9   -- 27

-- compose f with f
def applyTwice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

#eval applyTwice Triple 5   -- 45

-- currying

-- addition of two natural number
def add : Nat → Nat → Nat := fun x y => x + y

-- add 3 to the input number
def addThree : Nat → Nat := add 3

#check addThree    -- function_type.addThree : ℕ → ℕ

#eval addThree 2    -- 5

-- Function composition
def compose {A B C : Type}
  (f : B → C) (g : A → B) : A → C := fun x => f (g x)

-- def two functions
def inc (n : Nat) : Nat := n+1  
def square (n : Nat) : Nat := n*n

#eval compose inc square 6   -- 37
#eval compose square inc 6   -- 49

end function_type

namespace unit_type
 
example (e1 e2 : Unit) : e1 = e2 := rfl 

inductive CustomUnit where
| customUnit

example (e1 e2 : CustomUnit) : e1 = e2 := rfl 

def constant_function : Unit → Nat := 
  fun () => 42

#check constant_function     -- unit_type.constant_function : Unit → ℕ

#eval constant_function ()   -- 42

def placeholderPair : Nat × Unit := (25, Unit.unit)

def placeholderPair2 : Nat × Unit := (125, ())

#eval placeholderPair.1    -- 25
#eval placeholderPair.2    -- PUnit.unit

-- unit for side effect
-- IO Unit represent an action with no meaningful return value
def greeting : IO Unit :=
  IO.println "Hello World"

#check greeting   -- unit_type.greeting : IO Unit

#eval greeting   -- print "Hello World" in InfoView

end unit_type




namespace empty_type

def fromEmptyToNat : Empty → Nat := 
  fun e => nomatch e -- no case to match

-- the second option is impossible
inductive Weird where 
| ok : Nat → Weird
| bad : Empty → Weird

def processWeird : Weird → Nat 
| Weird.ok n => n
| Weird.bad e => nomatch e  -- unreachable code

-- test
#eval processWeird (Weird.ok 34)    -- 34

end empty_type
