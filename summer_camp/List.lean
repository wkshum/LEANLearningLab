/-
  List type, join, filter, flatten
-/


namespace hidden

-- 1. definition list on A / free monoid on A
inductive List (A :Type)
  | nil
  | cons (a:A) (l: List A)

-- 2. List Multiplication
def List.mul {A : Type} : List A → List A → List A :=
 fun a b ↦ match a, b with
 | nil, b => b
 | cons a as, b => cons a (List.mul as b)

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

/-    Flattening is simply collapsing a List of Lists into a single List
    by multiplying (appending) them all together. -/
def List.flatten {A : Type} (l : List (List A)) : List A :=
  List.join l

/-- flatMap is the cornerstone of functional programming.
    It maps a function that creates lists, and then flattens the result.
    Notice how `filter` was just a specific instance of `flatMap`! -/
def List.flatMap {A B : Type} (f : A → List B) (l : List A) : List B :=
  List.flatten (List.map f l)


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

end hidden
