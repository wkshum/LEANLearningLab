/-
lecture2
-/

import Mathlib.Tactic

-- prove 2^n ≥ n+1 for n ≥ 0

theorem t1 (n:ℕ): 2^n ≥ n+1 := by
  induction' n with n ih
  · -- base case
    rfl
  · -- induction step
    calc
      2^(n+1) = 2*(2^n) := by ring
            _ ≥ 2*(n+1) := by rel [ih]
            _ = (n+1+1)+n := by ring
            _ ≥ (n+1+1)+0 :=
                  by rel [Nat.zero_le n]
            _ = n+1+1 := by ring


example : 3 ∣ 12 := by
--  dsimp [Dvd.dvd]
  dsimp [(· ∣ ·)]
  use 4

def f (n:ℕ) := n^3+2*n

#eval f 19
-- Prove 3 divides n^3+2*n

example (n:ℕ) : 3 ∣ (n^3 + 2*n) := by
  induction' n with m ih
  · dsimp[Dvd.dvd]  -- base case
    apply Exists.intro 0
    norm_num
  · -- induction step
    dsimp [Dvd.dvd]
    obtain ⟨a , ha⟩ := ih
    use m^2+m+1+a
    calc
      (m+1)^3+2*(m+1)
       = 3*m^2+3*m+3+ (m^3+2*m) := by ring
      _= 3*m^2+3*m+3+ (3*a) := by rw [ha]
      _= 3*(m^2+m+1+a) := by ring

open Finset
open BigOperators

def S (n:ℕ) := ∑ x in (range (n+1)), 2^x

#eval S 2

-- Prove ∑_{k=0}^n 2^k + 1 = 2^(n+1)

-- Prove ∑_{k=0}^n 2^k + 1 = 2^(n+1)

example (n:ℕ) : ∑ x in range (n+1), 2^x + 1= 2^(n+1) := by
  induction' n with k ih
  · rfl
  · -- induction step
    show ∑ x in (range (k+2)), 2^x + 1 = 2^(k+2)
    calc
      ∑ x in (range (k+2)) , 2^x + 1
      = ∑ x in (range (k+1)), 2^x +  2^(k+1) + 1 :=
          by rw [sum_range_succ]
    _ = (∑ x in (range (k+1)), 2^x + 1) + 2^(k+1)  := by ring
    _ = 2^(k+1) + 2^(k+1) := by rw [ih]
    _ = 2^(k+2) := by ring




/-
 Prove that 1^2 + 2^2 + 3^2 + ... + n^2 = n*(n+1)*(2n+1)/6 for n ≥ 1
-/

-- We want to show that the functions U1 and U2 defined below are the same
def U1 (n:ℕ) := ∑ k in (range (n+1)), k^2
def U2 (n:ℕ) := n*(n+1)*(2*n+1)/6

#eval U1 2  -- 55
#eval U2 2  -- 55


example {n:ℕ} (h1: n≥ 1) : ∑ k in (range (n+1)), k^2 = n*(n+1)*(2*n+1)/6 := by
  have claim : 6 * ∑ k in (range (n+1)), k^2 = n*(n+1)*(2*n+1) := by
    induction' n, h1 using Nat.le_induction with n _ ih
    · rfl
    · calc
         6*∑ k in (range (n+2)), k^2
       = 6*(∑ k in (range (n+1)), k^2  + (n+1)^2 ) := by rw [sum_range_succ]
      _= 6*∑ k in (range (n+1)), (k)^2  + 6*(n+1)^2 := by ring
      _= n*(n+1)*(2*n+1) + 6*(n+1)^2 := by rw [ih]
      _= (n+1)*(n+2)*(2*(n+1)+1) := by ring
  refine Nat.eq_div_of_mul_eq_right ?_ claim
  linarith



def T1 (n:ℕ) := ∑ k in (range (n+1)), (2*k-1)^2
def T2 (n:ℕ) := (4*n^3 - n)/3
-- When k=0, the term (2*k-1), as a number with type ℕ, is equal to 0

#eval T1 0
#eval T2 0


-- Prove ∑_{k=1}^n (2k-1)^2 = (4n^3 - n)/3 for n ≥ 1
-- Fuchs Problem 4.1.a
example (n:ℕ) (h1 : n ≥ 1): ∑ k in (range (n+1)), (2*k-1)^2 = (4*n^3-n)/3 := by
  have claim : 3 * ∑ k in (range (n+1)), (2*k-1)^2 = 4*n^3-n := by
    induction' n, h1 using Nat.le_induction with n hn ih
    · rfl  -- base case
    · -- induction step
      have hn1 : 4*n^3 ≥ n := by
        calc
        4*n^3 = 4*n^2 *n := by ring
              _ ≥ 4 *(1)^2 * n := by rel [hn]
              _ ≥ 1 * n := by refine Nat.mul_le_mul_right n ?_
                              linarith
              _ = n := by ring

      calc
        3*∑ k in (range (n+2)), (2*k-1)^2
        = 3*(∑ k in (range (n+1)), (2*k-1)^2 + (2*(n+1)-1)^2) :=
            by rw [sum_range_succ]
      _ = 3*(∑ k in (range (n+1)), (2*k-1)^2) + 3*(2*(n+1)-1)^2 := by ring
      _ = (4*n^3-n) + 3*(2*(n+1)-1)^2 := by rw [ih]
      _ = (4*n^3-n) + 3*(2*n+1)^2 := by rfl
      _ = 4*n^3 -n + (12*n^2 + 12*n + 3)  := by ring
      _ = 4*n^3 + (12*n^2 + 12*n +3) -n  := (Nat.sub_add_comm hn1).symm
      _ = 4*n^3 + (12*n^2 + 12*n + 3) + 1 - 1 - n := by rfl
      _ = 4*n^3 + 12*n^2 + 12*n + 4 -1 - n := by ring_nf
      _ = 4*n^3 +12*n^2 + 12*n + 4 - (n + 1) := by simp
      _ = 4*(n+1)^3 - (n+1) := by ring_nf

  refine Nat.eq_div_of_mul_eq_right ?_ claim
  linarith

/-
 Define a sequence (a_n), for n=1,2,3,..., by
a_1 = 3
a_{n+1} = a_n + 6n(n+1)   for n≥1

Prove that a_n = 2n^3 - 2n + 3 for n≥1
-/


-- Define the sequence (a_n) recursively
def a : ℕ → ℕ
 | 0 => 3
 | n+1 => a n + 6 * n * (n+1)

#eval a 13


example (n: ℕ) (h : n ≥ 1) : a n = 2*n^3 - 2*n + 3 := by
  induction' n, h using Nat.le_induction with n hn ih
  · rfl  -- base case
  · have hn1 :  2*n^3 ≥ 2*n := by
      calc  2*n^3 = 2*n^2*n := by ring
                _ ≥  2*(1)^2*n := by rel [hn]
                _ ≥ 2*n := by refine Nat.mul_le_mul_right n ?_
                              linarith
                _ = 2*n := by ring

    have hn2 : 2*(n+1)^3 ≥ 2*(n+1) := by
      calc
        2*(n+1)^3 = 2*(n+1)^2*(n+1) := by ring
                _ ≥ 2*(1)^2*(n+1) := by rel [Nat.le_add_left 1 n]
                _ = 2*(n+1) := by ring

    calc
     a (n+1) = a n + 6 * n * (n+1) := by rfl
           _ = (2*n^3 - 2*n + 3) + 6*n*(n+1) := by rw [ih]
           _ = 2*n^3 - 2*n + (3 + 6*n*(n+1)) := by ring
           _ = 2*n^3 + (3 + 6*n*(n+1)) - 2*n  := (Nat.sub_add_comm hn1).symm
           _ = (2*n^3 + 3 + 6*n^2 + 6*n) - 2*n   := by ring_nf
           _ = (2*n^3 + 3 + 6*n^2 + 6*n) + 2 - 2 - 2*n   := by rfl
           _ = 2*n^3 + 3 + 6*n^2 + 6*n + 2 - (2*n + 2)  :=
                     (Nat.Simproc.sub_add_eq_comm _ (2*n) 2).symm
           _ = 2*(n+1)^3 + 3 - 2*(n+1)  := by ring_nf
           _ = 2*(n+1)^3 - 2*(n+1) + 3 := (Nat.sub_add_comm hn2)




/-
 Prove that the n-th Fibonacci number is less than 2^n
-/


namespace Fib
def F : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n+2 => F (n+1) + F n

#eval F 2


example  (n: ℕ) : F n ≤ 2^n := by
  induction' n using Nat.twoStepInduction with k ih1 ih2
  · rfl   -- base case 1
  · simp [F]   -- base case 2
  · -- inductive step
    calc
      F (k+2) = F (k+1) + F k := by rfl
            _ ≤ 2^(k+1) + 2^k := by rel [ih1, ih2]
            _ = 3*2^k := by ring
            _ ≤ 4*2^k := by refine Nat.mul_le_mul ?_ (Nat.le_refl (2^k))
                            norm_num
            _ = 2^(k+2) := by ring


end Fib
