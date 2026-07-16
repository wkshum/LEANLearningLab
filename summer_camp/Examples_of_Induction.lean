/-
Copyright (c) 2025 Kenneth Shum All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenneth Shum
-/

/- Example of proving theorems using mathematical induction in LEAN
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

open Finset BigOperators

section induction_examples

/-
 Prove that 1 + 2 + 2^2 + ... + 2^n = 2^(n+1)
 for all n ≥ 0

 Use induction on n. The base case is trivial if LHS
 is understood as 1 if n=0.  We write the sum 1 + 2 + 2^2 + ... + 2^n as
 (∑ k ∈ range (n+1) , 2^k) + 1, so that the value is 0 when n=0.
-/

example (n:ℕ) : (∑ k ∈ range (n+1) , 2^k) + 1 = 2^(n+1) := by
  induction' n with m ih
  · -- base case
    rfl
  · -- In the induction step, we need to show
    show ∑ k ∈ range (m + 1 + 1), 2 ^ k + 1 = 2 ^ (m + 1 + 1)

    -- replace `∑ k ∈ range (m + 1 + 1), 2 ^ k` by
    -- `∑ x ∈ range (m + 1), 2 ^ x + 2 ^ (m + 1)`
    rw [sum_range_succ]

    calc
       ∑ x ∈ range (m + 1), 2 ^ x + 2 ^ (m + 1) + 1
     _= ∑ x ∈ range (m + 1), 2 ^ x + 1 + 2 ^ (m + 1) := by ring
     _= 2 ^ (m + 1) + 2^(m+1) := by rw [ih]
     _= 2 ^ (m + 1 + 1) := by ring


/-  prove 2^n ≥ n+1 for n≥ 0
-/
example (n:ℕ) : 2^n ≥ n+1 := by
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



/-
 Prove 3^n ≥ 2^n + 5 for n ≥ 2
-/

example {n:ℕ} (hn: 2≤n) : 3^n ≥ 2^n+5 := by
  induction' n, hn using Nat.le_induction with k _ ih
  · -- base case
    norm_num
  · -- induction step
    have h₁ : 2^k+10 ≥ 0 := by positivity
    calc
       3^(k+1) = 3*3^k := by ring
             _ ≥ 3*(2^k+5) := by rel [ih]
             _ = 2^(k+1)+5 + (2^k+10) := by ring
             _ ≥ 2^(k+1)+5 + 0 := by rel [h₁]



/-

Prove that 1+2^2+3^2+...+n^2 = n*(n+1)*(2*n+1)/6
for n≥ 1

For ease of proof, we prove it an equivalent form
6(1+2^2+3^2+...+n^2) = n*(n+1)*(2*n+1)
-/

theorem six_mul_sum_Ico_square {n:ℕ} (hn : n≥ 1) :
  6* ∑ k ∈ Ico 1 (n+1), k^2 = n*(n+1)*(2*n+1) := by
  induction' n, hn using Nat.le_induction with n _ ih
  · -- base case
    simp
  · -- induction step
    -- we wan to show
    show 6 * ∑ k ∈ Ico 1 (n + 1 + 1), k ^ 2 = (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1)

    -- reduce to the induction hypothesis
    have : 1≤ n+1 := by exact Nat.le_add_left 1 n
    rw [Finset.sum_Ico_succ_top this]

    -- we now need to show
    show 6 * (∑ k ∈ Ico 1 (n + 1), k ^ 2 + (n + 1) ^ 2) = (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1)

    calc
          6 * (∑ k ∈ Ico 1 (n + 1), k ^ 2 + (n + 1) ^ 2)
      _= 6 * (∑ k ∈ Ico 1 (n + 1), k ^ 2) + 6*(n+1)^2 := by ring
      _= (n * (n + 1) * (2 * n + 1)) + 6*(n+1)^2 := by rw [ih]
      _= (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1) := by ring



/-
Prove that 1+2^2+3^2+...+n^2 = n*(n+1)*(2*n+1)/6
for n≥ 1
-/
theorem mul_sum_Ico_square {n:ℕ} (hn : n≥ 1) :
  ∑ k ∈ Ico 1 (n+1), k^2 = n*(n+1)*(2*n+1)/6 := by
  rw [← six_mul_sum_Ico_square hn]
  have : 0<6 := by norm_num
  rw [mul_comm]
  rw [Nat.mul_div_cancel _ this]



/-
Define a sequence a_n recursively by
a_0 := 3
a_{n+1} := a_n + 6n(n+1)  for n≥ 0

Proves that a_n = 2n^3-2n+3 for n≥ 0
-/

def a : ℕ → ℕ
 | 0 => 3
 | n+1 => a n + 6*n*(n+1)


example (n:ℕ) (hn : n≥1 ) : a n = 2*n^3 - 2*n+3 := by
  induction' n, hn using Nat.le_induction with n hn ih
  · -- base case is trivial
    rfl
  · -- induction step
    show a (n + 1) = 2 * (n + 1) ^ 3 - 2 * (n + 1) + 3

    simp only [a] -- replace a (n+1) by its definition
    rw [ih]  -- apply the induction hypothesis

    -- we want to show
    show 2*n^3 - 2*n + 3 + 6*n*(n+1) = 2*(n+1)^3 - 2*(n+1) + 3

    -- we need an inequality in the calculation
    have ineq (k:ℕ) (hk: k≥ 1) : 2*k^3 ≥ 2*k := by
      calc
        2*k^3 = k^2*(2*k) := by ring
            _ ≥ 1*(2*k) := by rel [(Nat.one_le_pow 2 k hk)]
                  --rel [Nat.mul_le_mul_right (2*k) (Nat.one_le_pow 2 k hk)]
            _ = 2*k := by ring

    calc
      2*n^3 - 2*n + 3 + 6*n*(n+1)
      _ = 2*n^3 - 2*n + (3 + 6*n*(n+1)) := by ring
      _ = 2*n^3 + (3 + 6*n*(n+1)) - 2*n := (Nat.sub_add_comm (ineq n hn)).symm
      _ = 2*n^3 + 3 + 6*n^2 + 6*n - 2*n := by ring_nf
      _ = 2*n^3 + 3 + 6*n^2 + 6*n + 2 - 2 - 2*n := by rfl
      _ = 2*n^3 + 3 + 6*n^2 + 6*n + 2 - (2*n+2)  := by
            exact (Nat.Simproc.sub_add_eq_comm _ (2*n) 2).symm
      _ = 2*(n+1)^3 + 3 - 2*(n+1) := by ring_nf
      _ = 2*(n+1)^3 - 2*(n+1) + 3 := Nat.sub_add_comm (ineq (n+1) ?_)

    exact Nat.le_add_left 1 n   -- proof of n+1 ≥ 1



end induction_examples
