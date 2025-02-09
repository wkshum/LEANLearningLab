/-
Copyright (c) 2025 Kenneth Shum All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenneth Shum
-/

/-
  Example of verifying the roots of a polynomial
-/


import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic

section Cardano


/-
Cardano equation

Show that the cubie equation x^3-6*x^2+11*x-6=2*x-2 has roots 1 and 4

-/


/-
  Cardano equation

  Show that the cubic polynomial x^3-6*x^2+11*x-6=2*x-2 has roots 1 and 4
-/

-- If x satisfies the equation has roots, then x is either 1 or 4
theorem cardano1 (x:ℝ): x^3-6*x^2+11*x-6=2*x-2 → x=1 ∨ x=4 := by
  intro h

  -- factorize the polynomial
  have h1 : (x-4)*((x-1)*(x-1)) = 0 :=
    calc
      (x-4)*((x-1)*(x-1))
      = (x^3-6*x^2+11*x-6) - (2*x-2) := by ring
    _ = (2*x-2) - (2*x-2) := by rw [h]
    _ = 0 := by ring

  -- deduce x=4 ∨ x=1 from hypothesis h1
  obtain ha | hb := eq_zero_or_eq_zero_of_mul_eq_zero h1
  · exact Or.inr (sub_eq_zero.mp ha)
  · have h3 : x-1=0 ∨ x-1=0 := eq_zero_or_eq_zero_of_mul_eq_zero hb
    obtain h4 | h4 := h3
    repeat exact Or.inl (sub_eq_zero.mp h4)

-- 1 and 4 satisfy Cardano's equation
theorem cardano2 (x:ℝ): x=1 ∨ x=4 → x^3-6*x^2+11*x-6=2*x-2 := by
  intro h
  obtain h1|h4 := h
  · -- assume x=1
    rw [h1]
    ring
  · -- assume x=4
    rw [h4]
    ring

-- The only roots of Cardano's equation are 1 and 4
theorem cardano (x:ℝ):  x^3-6*x^2+11*x-6=2*x-2 ↔ x=1 ∨ x=4 := by
  constructor
  · exact cardano1 x
  · exact cardano2 x


end Cardano




section roots_of_minus_three
/-
  Prove that the square roots of -3 are the roots of x^2+3=0.

  The difficulty in the proof is the coecion between the
  Complex type and the Real type.
-/

open Complex

-- We need some functions on how to deal with square root of 3
example : (Real.sqrt 3)^2 = 3:= by
  have three_gt_zero : (3:ℝ) ≥ 0 := by norm_num
  exact Real.sq_sqrt three_gt_zero

example (r s  :ℝ) (h : r = s ) : Complex.ofReal r =  s := by
   exact congrArg (⇑ofReal) h

example  : (Complex.ofReal √3)^2  = Complex.ofReal (√3^2) := by
   exact (RingHom.map_pow ofReal √3 2).symm


-- If z^2=-3, then z equals √3i or -√3i
lemma sqrt_minus_3a  (z:ℂ) : z^2 = -3  → z= (Real.sqrt 3)*I ∨ z= -(Real.sqrt 3)*I := by
  intro h
  have h0 :√3^2 = 3 := by
    refine Real.sq_sqrt ?_
    linarith
  have h1 : (z+√3*I)*(z-√3*I) = 0  := by
   calc
    (z+√3*I)*(z-√3*I) = z^2 - ((√3)^2)*(I*I) := by ring
                    _ = -3 - ((√3)^2)*(I*I) := by rw [h]
                    _ = -3 - (√3)^2*(-1) := by rw [I_mul_I]
                    _ = -3 - ((√3)^2 : ℝ )*(-1) := by norm_cast
                    _ = -3 - (3:ℝ)*(-1) := by rw [h0]
                    _ = -3 + 3 := by norm_num
                    _ = 0 := by ring
  have h2 : z+√3*I=0 ∨ z-√3*I =0 := by exact mul_eq_zero.mp h1
  obtain h_eq1 | h_eq2 := h2
  · -- first solution
    right
    calc
      z  = (z+√3*I) - √3*I := by ring
       _ = 0 - √3*I := by rw [h_eq1]
       _ = - √3*I := by ring
  · -- second solution
    left
    calc
      z  = (z-√3*I) + √3*I := by ring
       _ = 0 + √3*I := by rw [h_eq2]
       _ = √3*I := by ring




-- the square of the square root of r is equal to r
-- with coecion to the complex type
lemma helper_lemma (r:ℝ) (hr : 0≤ r) :  (Complex.ofReal √r)^2 = r := by
    rw [(RingHom.map_pow ofReal √r 2).symm]
    refine congrArg (⇑ofReal) ?_
    exact Real.sq_sqrt hr

-- √3i and -√3i satisfy the equation z^2=-3
lemma sqrt_minus_3b  (z:ℂ) :  z= (Real.sqrt 3)*I ∨ z= -(Real.sqrt 3)*I → z^2 = -3  := by
  intro h

  have h₃  :  (Complex.ofReal √3)^2 = 3 := by
    refine helper_lemma 3 ?_
    norm_num

  obtain h1|h2 := h
  · -- case z = √3i
    rw [h1]
    calc
      (Complex.ofReal √3 * I) ^ 2 = (Complex.ofReal √3) ^2 * I^2 := by ring
                  _ = ((Complex.ofReal √3)^2) * (-1) := by rw [I_sq]
                  _ = (3:ℂ) * (-1) := by rw [h₃]
                  _ = -3 := by ring
  · -- case z = -√3i
    rw [h2]
    calc
      (-Complex.ofReal √3 * I) ^ 2 = (Complex.ofReal √3) ^2 * I^2 := by ring
                  _ = ((Complex.ofReal √3)^2) * (-1) := by rw [I_sq]
                  _ = (3:ℂ) * (-1) := by rw [h₃]
                  _ = -3 := by ring


-- The roots of z^2=-3 are precisely √3i and -√3i
theorem sqrt_of_minus_three (z:ℂ) :
  z^2 = -3  ↔  z= (Real.sqrt 3)*I ∨ z= -(Real.sqrt 3)*I  :=  by
  constructor
  · exact sqrt_minus_3a z
  · exact sqrt_minus_3b z






-- second proof of sqrt_minus_3b using `suffices`
example (z:ℂ) :  z= (Real.sqrt 3)*I ∨ z= -(Real.sqrt 3)*I → z^2 = -3  := by
  intro h
  have h₃  :  (Complex.ofReal √3)^2 = 3 := by
    refine helper_lemma 3 ?_
    norm_num

  suffices h_sqrt_minus3: (Complex.ofReal √3) ^2 * I^2 = -3 from ?_
  · obtain h1|h2 := h
    · rw [h1]
      rw [←h_sqrt_minus3]
      exact mul_pow (↑√3) I 2
    · rw [h2]
      calc
           (- Complex.ofReal √3 * I) ^ 2
       _ = (Complex.ofReal √3)^2 * I^2 := by ring
       _ = -3 := by rw [h_sqrt_minus3]

  · calc  -- show that the assumption h_sqrt_minus3 is valid
          (Complex.ofReal √3) ^2 * I^2
      _ = ((Complex.ofReal √3)^2) * (-1) := by rw [I_sq]
      _ = (3:ℂ) * (-1) := by rw [h₃]
      _ = -3 := by ring


end roots_of_minus_three
