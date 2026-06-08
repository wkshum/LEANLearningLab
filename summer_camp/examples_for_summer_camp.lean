import Mathlib.Tactic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Lattice

-- Logical AND

example (h : P ∧ Q) : P := by
   exact h.1

example (h : P ∧ Q) : Q := by
   exact h.2

example (hP : P) (hQ : Q) : P ∧ Q := by
  exact ⟨ hP, hQ⟩

  -- (Alternate proof)
  -- constructor
  -- · exact hP
  -- · exact hQ

-- Logical OR

example (hA : A) : A ∨ B := by
  left
  exact hA

example (hB : B) : A ∨ B := by
  right
  exact hB

-- prove a "for all" statement
example : ∀ n :ℕ , n+0 = n := by
  intro n
  ring

-- disprove a "for all" statement
example : ¬  ∀ n :ℕ , n+n = n := by
  intro h
  have hh : 1 + 1 = 1 := h 1
  contradiction


-- prove a "there exist" statement
example : ∃ n:ℕ , n+n = n := by
  use 0

-- disprove a "there exist statement"
example : ¬ ∃ n:ℕ , n = n+1 := by
  intro h
  obtain ⟨n, hn⟩ := h
  -- alternately, we can write
  -- rcases h with ⟨n, hn⟩
  -- to achieve the same effect

  omega -- omega sees `n = n + 1` in the hypotheses
  -- and realizes it is mathematically impossible.

/- omega is a SAT/SMT-style solver
   it can solve system of linear equations in Nat

  It runs the "Omega Test" algorithm
  (originally developed by William Pugh in 1991
  for compiler loop optimizations).

  The algorithm checks if there is any valid
  integer assignment that satisfies the constraints.
  If it mathematically proves no solution exists
  (or that the goal is universally true),
  it generates the exact Lean proof steps under
  the hood to satisfy the kernel.
-/


-- Example of Omega tactic: Proving impossible inequalities
example (n : ℕ) : ¬(n < 5 ∧ n > 8) := by omega

-- Omega can do tedious algebraic shuffling
example (x y : ℕ) (h : x + y = 10) (h2 : x = 3)
  : y = 7 := by omega


-- If x=1 or y=-1, then x*y+x = y+1
-- Solve by dividing into two cases
example (x y : ℝ) ( h : x=1 ∨ y=-1)
  : x*y+x = y+1 :=  by
  obtain hx | hy := h
  · calc
    x*y+x = 1*y + 1 := by rw [hx]
          _= y+1 := by ring
  · calc
    x*y+x = x*(-1)+x := by rw [hy]
          _=0 := by ring
          _= (-1) + 1 := by ring
          _= y + 1 := by rw [hy]


example (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Real)
(h1 : x2+x3 ≤ x4+x5) (h2 : x1+x4≤x6+x7)
(h3 : x5+x6≤x8+x9) : x1+x2+x3 ≤ x7+x8+x9 := by
  linarith
-- An alternate proof by calculations
-- calc
--   x1 + x2 + x3 = x1 + (x2 + x3) := by ring
--               _ ≤ x1 + (x4 + x5) := by rel [h1]
--               _ = (x1 + x4) + x5 := by ring
--               _ ≤ (x6 + x7) + x5 := by rel [h2]
--               _ = x7 + (x5 + x6) := by ring
--               _ ≤ x7 + (x8 + x9) := by rel [h3]
--               _ = x7 + x8 + x9   := by ring



/-
 Interval_cases tactic
-/

example (k:ℕ) (h1 : 1≤ k) (h2: k≤ 4) : k ∣ 12 := by
  interval_cases k
  repeat decide

example (k:ℕ) (h1 : 1≤ k) (h2: k≤ 4) : k ∣ 12 := by
  have h : 1=k ∨ 2 ≤ k := Nat.eq_or_lt_of_le h1

  -- Using `rfl` automatically substitutes k with 1 in the goal
  rcases h with h | h''
  · rw [← h]
    decide
  · have : 2 = k ∨ 3 ≤ k := Nat.eq_or_lt_of_le h''
    rcases this with rfl | h₄
    · decide
    · have : 3 = k ∨ 4 ≤ k := Nat.eq_or_lt_of_le h₄
      rcases this with rfl | h₆
      · decide
      · -- Here we have h2 : k ≤ 4 and h₆ : 4 ≤ k
        have h₇ : k = 4 := Nat.le_antisymm h2 h₆
        subst h₇
        decide


noncomputable section Equiv

open Equiv

/-
We construct a permutation (bijection) on the reals
using the structure-building where syntax
-/
abbrev addRight (a:ℝ) : Perm ℝ where
  toFun := fun (x:ℝ) ↦ x + a
  invFun := fun x ↦ x - a
  left_inv := by
    dsimp [Function.LeftInverse]
    intro x
    ring
  right_inv := by
    dsimp [Function.RightInverse]
    dsimp [Function.LeftInverse]
    intro x
    ring

/-
 We can use `addRight` like a function
-/
example (a:ℝ) :
    let α := addRight a
    ∀ x y, x - y = α x - α y := by
  dsimp
  intro x y
  ring

/- Given an equivalent relation α by invariance of distance.
  If input x and y has distance x- y, then
  the outpu α x - α y has distance x - y
-/
def IsTranslation (α : Perm ℝ) : Prop :=
  ∀ x y : ℝ , α x - α y = x - y

abbrev translationSubgroup : Subgroup (Perm ℝ) where
  carrier := {α | IsTranslation α }
  mul_mem' := by
    intro α β ha hb
    dsimp [IsTranslation] at *
    intro x y
    rw [ha (β x) (β y)]
    rw [hb x y]
  one_mem' := by
    dsimp [IsTranslation]
    intro x y
    rfl
  inv_mem' := by
    intro α
    dsimp
    intro ha
    dsimp [IsTranslation] at ha ⊢
    intro x y
    rw [← ha]
    simp


notation "T" => translationSubgroup

/-
If `α ∈ T` and `α 0 = a`, prove that `α x = x + a`
-/
example (α : Perm ℝ) (hα : α ∈ T) {a:ℝ} (h: α 0 = a) :
    α = addRight a := by
  ext x
  dsimp
  have H := hα x 0
  rw [h] at H
  linear_combination H

open Complex (I exp exp_add exp_zero re im )

def IsIsometry (α : ℂ → ℂ ) : Prop :=
  ∀ z w : ℂ , norm ( α z - α w ) = norm ( z - w )

example :
    let α := fun (z:ℂ) ↦ z+2*I
    ∀ z w , z - w = α z - α w := by
  dsimp
  intro z w
  ring

example :
    let α := fun (z:ℂ) ↦ z+2*I
    IsIsometry α := by
  dsimp [IsIsometry]
  intro z w
  abel_nf

abbrev translation (c:ℂ) : Perm ℂ where
  toFun := fun x ↦ x + c
  invFun := fun x ↦ x - c
  left_inv := by
    dsimp [Function.LeftInverse]
    intro x
    ring
  right_inv := by
    dsimp [Function.RightInverse]
    dsimp [Function.LeftInverse]
    intro x
    ring

abbrev rotation (θ : ℝ) : Perm ℂ where
  toFun := fun z ↦ exp (I * θ) * z
  invFun := fun z ↦ exp (-I * θ) * z
  left_inv := by
    dsimp [Function.LeftInverse]
    intro z
    calc
      exp (-I * θ) * (exp (I * θ) * z)
       = (exp (-I * θ) * exp (I * θ)) * z := by rw [mul_assoc]
      _= (exp (-I * θ + I * θ)) * z := by rw [exp_add]
      _= exp 0 * z := by ring_nf
      _= 1 * z := by rw [exp_zero]
      _= z := by ring
  right_inv := by
    dsimp [Function.RightInverse]
    dsimp [Function.LeftInverse]
    intro z
    calc
      exp (I * θ) * (exp (-I * θ) * z)
       = (exp (I * θ) * exp (-I * θ)) * z := by rw [mul_assoc]
      _= (exp (I * θ + (-I) * θ)) * z := by rw [exp_add]
      _= exp 0 * z := by ring_nf
      _= 1 * z := by rw [exp_zero]
      _= z := by ring



theorem isIsometry_rotation (θ : ℝ) : IsIsometry (rotation θ) := by
  dsimp [IsIsometry]
  intro z w
  calc
    ‖ exp (I * θ) * z - exp (I * θ) * w‖
    _ = ‖ exp (θ * I) * (z - w)‖  := by ring_nf
    _ = ‖ exp (θ * I)‖  * ‖ z - w‖  := by rw [Complex.norm_mul]
    _ = 1 * ‖z - w‖  := by rw [Complex.norm_exp_ofReal_mul_I θ]
    _ = ‖z - w‖  := by ring

end Equiv
