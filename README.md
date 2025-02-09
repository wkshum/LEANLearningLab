# LEANLearningLab
Illustration of computer formalization of mathematics.

In contrast to the philosophy of Mathlib, we do not push to the highest level of generality in the examples. For instance, a theorem is stated for real numbers, even though the statement holds for modules over commutative ring. This is more in tune with the approach in ["Mechanics of Proof"](https://hrmacbeth.github.io/math2001/) by Heather Macbeth. However, we will not use any tailor-made tactics. All programs should be compilable in the online LEAN server.

List of topics
- Roots_of_equation : Verify the roots of polynomial equation
- ExampleOfInductoin : Proof by mathematical induction
- SimplicialComplex : Re-writing Chapter 3 of Loh's "Exploring formalization" in LEAN4
- ComputableComplexNumber : Formalization of the number field Q[i], the quotient field of the Gaussian integers. This is similar to the  [Complex](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Complex/Basic.html) type in Mathlib, except that the real and imaginary parts are rational numbers, so that the functions are computable.
