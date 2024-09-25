/-
 LEAN Learning lab
9/25/2024

Two examples of mathematical induction

-/

import Mathlib.Tactic

-- prove 2^n ≥ n+1 for n≥ 0

theorem test (n:ℕ) : 2^n ≥ n+1 := by
  induction' n with n ih
  · -- base case
    rfl
  · -- induction step
    calc
      2^(n+1) = 2^n*2 := by ring
            _ ≥ (n+1)*2 := by rel [ih]
            _ = (n+1+1)+n := by ring
            _ ≥ (n+1+1)+0 := by rel [Nat.zero_le n]
            _ = n+1+1 := by ring

example (n:ℕ) : n≥ 0 := by
  exact Nat.zero_le n

open Finset
open BigOperators

def S (n:ℕ) := ∑ x in (range (n+1)), 2^x

#eval S 31

-- Prove ∑_{x=0}^n 2^x + 1 = 2^n+1

example (n:ℕ) : (∑ x in range (n+1), 2^x) + 1
 = 2^(n+1) := by
 induction' n with k ih
 · -- base case
   rfl
 · -- induction step
   calc
    ∑ x in (range (k+2)), 2^x + 1
    = ∑ x in (range (k+1)), 2^x + 2^(k+1)+1
      := by rw [sum_range_succ]
   _= ∑ x in (range (k+1)), 2^x + 1 + 2^(k+1)
      := by ring
   _ = 2^(k+1) + 2^(k+1) := by rw [ih]
   _ = 2^(k+2)  := by ring
