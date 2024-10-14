/- Lean Learning Lab Tutorial

Oct 9, 2024

Logical operations

-/

import Mathlib.Tactic

-- Logical AND



-- If P AND Q, then P
example (h: P ∧ Q ) : P  := by
  exact h.1

-- If P AND Q, then Q
example (h: P ∧ Q ) : Q := by
  exact h.2

-- If P AND Q, then Q and P
example (h : P∧ Q) : Q∧ P := ⟨ h.2, h.1 ⟩

-- Another proof of if P AND Q then Q AND P
example (h : P∧ Q) : Q∧ P := by
  constructor
  · exact h.2
  · exact h.1

-- Logical OR

-- If A, then A OR B
example (ha :A) : A ∨ B := by
  exact Or.inl ha

-- If B, then A OR B
example (hb :B) : A ∨ B := by
  exact Or.inr hb

-- An example for Mechanics of Proof
-- Show that if x=1 OR y=1, then x*y+x = y+1
example (x y : ℝ) (h : x=1 ∨ y= -1) :
  x*y+x=y+1  := by
  obtain hx | hy := h
  calc
    x*y+x = 1*y + 1 := by rw [hx]
        _ = y+ 1 := by ring
  calc
    x*y+x = x*(-1)+x := by rw [hy]
 --       _ = 0 := by ring
        _ = (-1)+1 := by ring
        _ = y+1 := by rw [hy]



-- Existential quantifier


-- Prove that there exists an integer x that is
--   larger than 3
example : ∃ (x:ℤ), x>3 := by
  use 4
  linarith

-- another example of x that is larger than 3
example : ∃ (x:ℤ), x>3 := by
  use 100
  linarith

-- b^2+1 ≥ 0 for all rational number b
lemma test (b:ℚ) : b^2+1 ≥ 0 := by
  refine Rat.add_nonneg ?_ rfl
  exact sq_nonneg b

-- if a=b^2+1 for some b, then a ≥ 0
example (a:ℚ) (h: ∃ b:ℚ, a=b^2+1) :
  a ≥ 0 := by
  obtain ⟨b,hb⟩ := h
  calc
    a = b^2+1 := by exact hb
     _≥  0 := by exact test b



-- For all

-- if f x = 2*x for all x, then f 1 = 2
example (f:ℕ→ ℕ) ( h : ∀ x:ℕ , f x = 2*x) :
  f 1 = 2 := by
  exact h 1

-- x^2 = x*x for all x
example : ∀ x :ℕ , x^2=x*x := by
  intro a
  exact Nat.pow_two a

-- if n | m for all m, then n=1
example (n:ℕ) (hn : ∀ m , n ∣ m) : n = 1 :=
  by
  exact Nat.eq_one_of_dvd_one (hn 1)
