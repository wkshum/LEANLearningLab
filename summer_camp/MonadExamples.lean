import Mathlib.Tactic

/-
## Monad
-/

/-
  pure x wraps a value into a successful computation: some x.
  bind sequences computations:

  if the first step is none, the whole thing is none;
  if it is some a, then continue with f a.
-/

def safeDiv (a b : Int) : Option Int :=
  if b == 0 then none else some (a / b)


#eval do
  let mut x ← safeDiv 10 2
  let mut y ← safeDiv x 0
  pure (x + y)   -- evaluates to none

def example2 : Option Int :=
  safeDiv 10 2 >>=
  fun x => safeDiv x 0 >>=
  fun y => pure (x + y)

#eval example2

instance : Monad Option where
  pure := some
  bind
    | none,     _ => none
    | some a, f => f a


/-
  ## List
-/

#check List

/-
`List.join` takes a list of lists and flattens it into a single list.

Examples:
  join [[1,2], [3], [4,5]] = [1,2,3,4,5]

This function is essential for the List monad because `bind` produces
a *list of lists*, and `join` removes one layer of list structure.
-/
def List.join : List (List α) → List α
  | []      => []
  | x :: xs => x ++ join xs


/-
A simple test:
`List.join [[1,2], [], [3,4]]` should flatten the nested list.

Expected result:
  [1, 2, 3, 4]
-/
#eval List.join [[1,2], [], [3,4]]


/-
We now declare that `List` is a monad.

A monad needs two operations:

1. `pure : α → List α`
     Wrap a value into a trivial list containing just that value.

2. `bind : List α → (α → List β) → List β`
     Apply the function `f` to every element of the list `xs`,
     producing a list of lists, then flatten the result using `join`.

This gives the List monad its interpretation as *nondeterministic computation*:
a list represents many possible outcomes, and `bind` explores all possibilities.
-/
instance : Monad List where
  pure a := [a]
  bind xs f := List.join (xs.map f)



#eval (pure 5 : List Int)   -- [5]

-- the same result as pure 5 as a term in List Int
#eval
  let xs : List Int := pure 5
  xs

def neighbors (n : Int) : List Int :=
  [n - 1, n + 1]

#eval ([10, 15] >>= neighbors)
-- [9,11, 14, 16]

/-
Explanation:

neighbors of 10 → [9, 11]
neighbors of 15 → [14, 16]

flatten → [9, 11, 14, 16]
-/

#eval do
  let mut x ← (pure 10 : List Int)
  let mut y ← neighbors x
  return (x+y)

-- evaluated to [19, 21]
