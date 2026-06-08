/-
  This Lean program defines List type, and
  illustrate functional programming

  We will see join, filter, and flatten in this program.

  All examples can be repeated in Python. But in Python we cannot
  do mathematical proof.
-/


namespace hidden

-- 1. definition list on A / free monoid on A
inductive List (A :Type)
  | nil
  | cons (a:A) (l: List A)
  deriving Repr


-- examples of list
def list1 : List Nat := .cons 1 (.cons 2 (.cons 3 .nil))
-- List.cons 1 (hidden.List.cons 2 (hidden.List.cons 3 (hidden.List.nil)))

def list2 : List Nat := .cons 4 (.cons 5 .nil)
-- List.cons 4 (hidden.List.cons 5 (hidden.List.nil))

#eval list1
#eval list2



-- macro rules for defining and printing a term of type List
macro_rules
  -- Rule 1: Empty brackets translate to `nil`
  | `([ ]) => `(List.nil)
  -- Rule 2: A single item translates to `cons x nil`
  | `([ $x ]) => `(List.cons $x List.nil)
  -- Rule 3: Multiple items: pop the first item off, and recursively call the macro on the rest!
  | `([ $x, $xs,*, $y ]) => `(List.cons $x [ $xs,*, $y ])
  | `([ $x, $xs,* ]) => `(List.cons $x [ $xs,* ])

-- Helper function: turns [| 1, 2 |] into the string "1, 2"
def List.reprHelper {A : Type} [Repr A] : List A → Std.Format
  | nil => ""
  | cons a nil => repr a
  | cons a as => repr a ++ ", " ++ reprHelper as

-- Now we register it to Lean's `Repr` typeclass
instance {A : Type} [Repr A] : Repr (List A) where
  reprPrec l _ := "[" ++ List.reprHelper l ++ "]"

def myEasyList : List Nat := [ 1, 2, 3 ]

#eval myEasyList -- [1,2,3]
#eval list1   -- [1,2,3]
#eval list2   -- [4,5]


-- 2. List Multiplication
def List.mul {A : Type} : List A → List A → List A :=
 fun a b ↦ match a, b with
 | nil, b => b
 | cons a as, b => cons a (List.mul as b)

-- Example of `mul`
example : list1.mul list2 = .cons 1 (.cons 2 (.cons 3 (.cons 4 (.cons 5 .nil)))) := by
  rfl

#eval list1.mul list2 -- [1,2,3,4,5]



-- List multiplication is associative
theorem List.mul_assoc {A : Type} (a b c : List A) :
  (a.mul b).mul c = a.mul (b.mul c) := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [List.mul, ih]


-- 3. Functorial Map: Applies a function to every element
def List.map {A B : Type} (f : A → B)
  : List A → List B :=
  fun a ↦ match a with
  | nil => nil
  | cons x xs => cons (f x) (List.map f xs)

-- Let's double every number in list1
def double (n : Nat) : Nat := n * 2

#eval List.map double list1 -- [2,4,6]

example : List.map double list1 = .cons 2 (.cons 4 (.cons 6 .nil)) := by
  rfl

-- a prettier way to write the above example
example : List.map double list1 = [2,4,6] := by
  rfl


-- 4. Monadic Join: Flattens a List of Lists using `mul`
def List.join {A : Type} : List (List A) → List A :=
  fun l ↦ match l with
  | nil => nil
  | cons xs xss => xs.mul (List.join xss)


-- 5. The Guard Function
-- Note the `[DecidablePred p]`. This tells Lean: "Assume we have an
-- algorithm that can definitively compute True or False for `p a`."
def guard {A : Type} (p : A → Prop) [DecidablePred p] (a : A) : List A :=
  if p a then
    List.cons a List.nil
  else
    List.nil

-- 6. The Filter Function and the flatten function
def List.filter {A : Type} (p : A → Prop) [DecidablePred p]
  (l : List A) : List A :=
  List.join (List.map (guard p) l)

-- Let's filter out only the even numbers from [1, 2, 3, 4, 5]
def isEven (n : Nat) : Prop := n % 2 = 0

-- make `n%2=0` decidable
instance (n : Nat) : Decidable (isEven n) :=
  -- Lean's core provides `inferInstance` to fetch the decidability of `x = y`.
  -- We cast it to apply to our `isEven` definition.
  inferInstanceAs (Decidable (n % 2 = 0))

def list3 : List Nat := list1.mul list2  -- [1, 2, 3, 4, 5]

#eval List.filter isEven list3

example : List.filter isEven list3 = .cons 2 (.cons 4 .nil) := by
  -- `rfl` will compute the join(map(guard)) logic
  rfl

-- the same example written more concisely
example : List.filter isEven list3 = [2,4] := by rfl


/-    Flattening is simply collapsing a List of Lists into a single List
    by multiplying (appending) them all together. -/
def List.flatten {A : Type} (l : List (List A)) : List A :=
  List.join l

def nested_list : List (List Nat) := .cons list1 (.cons list2 .nil)

#eval nested_list   -- [[1, 2, 3], [4, 5]]
#eval List.flatten nested_list

-- The flattened nested_list is the same as [1,2,3,4,5]
example : List.flatten nested_list = [1,2,3,4,5] := by rfl



/-- flatMap is the cornerstone of functional programming.
    It maps a function that creates lists, and then flattens the result.
    Notice how `filter` was just a specific instance of `flatMap`! -/
def List.flatMap {A B : Type} (f : A → List B) (l : List A) : List B :=
  List.flatten (List.map f l)


def makePair (n : Nat) : List Nat := .cons n (.cons (n + 10) .nil)
def shortList : List Nat := .cons 1 (.cons 2 .nil)

#eval makePair 3  -- [3, 13]
#eval shortList  --  [1, 2]
#eval List.flatMap makePair shortList  -- [1, 11, 2, 12]

-- prove that List.flatMap makePair shortList
-- is equal to [1,11,2,12]
example : List.flatMap makePair shortList = [1,11,2,12] := by
  rfl

-- 8. a theorem about flattening
theorem join_mul {A : Type} (x y : List (List A)) :
  List.join (x.mul y) = (List.join x).mul (List.join y) := by
  induction x with
  | nil => rfl
  | cons xs xss ih =>
    -- Unfold join and mul in the goal.
    -- The goal becomes: xs.mul (xss.mul y).join = (xs.mul xss.join).mul y.join
    dsimp [List.join, List.mul]
    rw [ih]

    -- The goal is now: xs.mul (xss.join.mul y.join) = (xs.mul xss.join).mul y.join
    -- This is exactly associativity, but we need it backwards: a * (b * c) = (a * b) * c
    -- So we rewrite using the symmetric form of your mul_assoc theorem!
    rw [← List.mul_assoc xs (List.join xss) (List.join y)]

-- ==========================================
-- The Flattening Theorem
-- flatten (A * B) = flatten(A) * flatten(B)
-- ==========================================
theorem flatten_mul {A : Type} (x y : List (List A)) :
  List.flatten (x.mul y) = (List.flatten x).mul (List.flatten y) := by
  exact join_mul x y


-- The theorem says:
-- flatten([[1, 2]] * [[3], [4]]) = flatten([[1, 2]]) * flatten([[3], [4]])
def nested1 : List (List Nat) := .cons (.cons 1 (.cons 2 .nil)) .nil
def nested2 : List (List Nat) := .cons (.cons 3 .nil) (.cons (.cons 4 .nil) .nil)

#eval nested1   -- [[1, 2]]
#eval nested2   --[[3], [4]]
#eval List.flatten (nested1.mul nested2)  -- [1,2,3,4]
#eval (List.flatten nested1).mul (List.flatten nested2)  -- [1,2,3,4]


example : List.flatten (nested1.mul nested2) = (List.flatten nested1).mul (List.flatten nested2) := by
  -- We don't even need to compute it with `rfl`!
  -- We can just apply the theorem `join_mul`
  exact join_mul nested1 nested2



end hidden
