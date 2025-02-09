/-
Copyright (c) 2025 Kenneth Shum All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenneth Shum
-/


/-
In this file We prove that, given two finite sets X and Y with the same size,
and a function f from X to Y, the followings are equivalent:

* f is bijective
* f is injective
* f is surjective

Finite set X is represented as an element in `Finset α`, and
finite set Y is represented as an element in `Finset β`

We use two functions related to the pigeonhole principle from Mathlib:

`Finset.surj_on_of_inj_on_of_card_le`
(If f is an injective function from set X to set Y and |Y|≤|X|, then f is a surjection

`Finset.inj_on_of_surj_on_of_card_le`
(If f is an surjective function from set X to set Y and |X|≤|Y|, then f is a injection)


At the end of this file, we give a proof that there is no bijection
from a finite set to its proper subset.
-/



import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Classical     -- we need the choice function
open Set Finset


/-
The definition of `SurjOn f X Y` requires that for all y in Y
there exists an x of type `α` such that x is in X and f x = y

The definition of `InjOn f X` requires that for any two elements
x1 and x2 in X, we have `f x1 = f x2` implies `x1 = x2`.
-/


-- Illustration of the definition of `SurjOn`
-- If y ∈ Y, then there exists `x` in `X` such that `f x = y`
example {α β: Type*} {X : Finset α} {Y : Finset β} {y : β}
    {f : α → β} (h: Set.SurjOn f X Y) (hy : y ∈ Y)
  : ∃ x : α  , (x∈ X ∧ f x = y) := by
  -- unfold Set.SurjOn at h
  -- have y_in_image_of_f := h hy
  -- exact y_in_image_of_f
  exact h hy


-- Illustration of the definition of `InjOn`
example {α β: Type*} {X : Finset α} (f: α → β)
  (h : Set.InjOn f X)  -- assume f is injective on X
  : ∀ x1 ∈ X, ∀ x2 ∈ X, f x1 = f x2 → x1 = x2 := by
  dsimp [InjOn] at h
  intro x1 hx1 x2 hx2  -- suppose x1∈ X and x2∈ X
  intro h_equal        -- suppose f x1 = f x2
  show x1=x2
  exact h hx1 hx2 h_equal


-- Supppose X and Y are finite sets with the same cardinality
-- Prove that an injective function from X to Y is a bijection
--
theorem injection_on_finite_set_is_bijective {X : Finset α} {Y : Finset β} (f : α → β)
  (hf : ∀ x ∈ X, f x ∈ Y)   -- f maps X to Y
  (h_inj : InjOn f X)        -- assume that f is injective
  (h_card : X.card = Y.card)    -- assume X and Y have the same size
    : BijOn f X Y  := by        -- prove that f is a bijection

  -- Define a helper function θ that is basically the same as function f
  let θ (x : α) (_ht : x ∈ X) := f x

  have aux1 : ∀ (a₁ a₂ : α) (ha₁ : a₁ ∈ X) (ha₂ : a₂ ∈ X), θ a₁ ha₁ = θ a₂ ha₂ → a₁ = a₂
    := fun _ _ hy1 hy2 hk => h_inj hy1 hy2 hk

  have aux2 : Y.card ≤ X.card := Nat.le_of_eq (h_card.symm)

  -- f is surjective from X to Y
  have h_sur : SurjOn f X Y:= by
    -- show ↑X ⊆ (g '' ↑Y)
    intro x hx
    -- show ∃ y  ∈ Y, g y = x
    obtain ⟨y, hk1, hk2⟩ :=
      (Finset.surj_on_of_inj_on_of_card_le θ hf aux1 aux2 x) hx
    exact ⟨y, hk1, hk2.symm⟩

  -- f is a bijection
  exact ⟨hf, ⟨h_inj, h_sur⟩ ⟩



-- Supppose X and Y are finite sets with the same cardinality
-- Prove that a surjective function from X to Y is a bijection
--
theorem surjection_on_finite_set_is_bijective {X : Finset α} {Y : Finset β} (f : α → β)
  (hf : ∀ x ∈ X, f x ∈ Y)      -- f maps X to Y
  (h_sur : SurjOn f X Y)        -- assume that f is surjective
  (h_card : X.card = Y.card)    -- assume X and Y have the same size
    : BijOn f X Y  := by        -- porove that f is a bijection

  -- Define a helper function θ that is basically the same as function f
  let θ (x : α) (_ht : x ∈ X) := f x

  have aux1 : ∀ b ∈ Y, ∃ a, ∃ (ha : a ∈ X), θ a ha = b := by
    intro y hy
    obtain ⟨k, hk⟩ := h_sur hy
    exact ⟨k, hk.1, hk.2⟩

  have aux2 : X.card ≤ Y.card := by exact Nat.le_of_eq h_card

  -- f is injective on X
  have h_inj : InjOn f X := by
    dsimp [InjOn]
    intro x1 hx1 x2 hx2
    intro h_equal
    -- Assuming that f x1 =f x2, show that x1 = x2
    exact Finset.inj_on_of_surj_on_of_card_le θ hf aux1 aux2 hx1 hx2 h_equal

  -- f is a bijection
  exact ⟨hf , ⟨h_inj, h_sur⟩ ⟩

/-
The assumption that f maps X into Y, `∀ x ∈ X, f x ∈ Y`,can be removed.

In the following we prove the above theorem again without using the assumption
that f maps X into Y, because it is already implied by the other assumptions.
-/



/-
Using the choice function, we prove that a surjective function
has a right inverse. Then we show that the right inverse is injective
and surjective.
-/

-- Right inverse of surjective function exists
-- Assume X is a finite set of type α
--        f : α → β is surjective on X
-- Prove that f has right inverse g
theorem right_inverse_of_surjection {α β : Type*} [Inhabited α] {X : Finset α} {Y : Finset β}
      (f : α → β) (h: Set.SurjOn f X Y)
   : ∃ g : β → α, ∀ y ∈ Y , g y ∈ X ∧ f (g y) = y := by
  dsimp [Set.SurjOn] at h

  have hs (y : β) (hy : y ∈ Y): ∃ x' : α  , (x'∈ X ∧ f x' = y) := h hy

  -- define a function `inv`
  -- if y is not in Y, then `inv x` is the default element of type `α`
  -- if y is in Y, we use the `chooce` function to define `inv y`
  let inv := fun y : β =>
     if hy: y ∈ Y then Classical.choose (hs y hy) else default

  -- show that `inv` is the required inverse function of f
  use inv
  intro y hy
  dsimp [inv]
  rw [dif_pos hy]
  exact (Classical.choose_spec (hs y hy))



-- Supppose X and Y are finite sets with the same cardinality
-- Prove that a surjective function from X to Y is a bijection
--
-- The same function in already in Mathlib and
-- is called `surjection_on_finite_set_is_bijective`
--
theorem surjection_on_finite_set_is_bijective'
 {X : Finset α} {Y : Finset β} [Inhabited α] (f : α → β)
  (h_sur : SurjOn f X Y)        -- assume that f is surjective from X to Y
  (h_card : X.card = Y.card)    -- assume X and Y have the same size
    : BijOn f X Y  := by        -- porove that f is a bijection

  dsimp [SurjOn] at h_sur

   -- function f has a right inverse g
  obtain ⟨g, hg⟩ := right_inverse_of_surjection f h_sur

  -- The function g is one-to-one on Y
  have g_inj : InjOn g Y:= by
    intro y1 hy1 y2 hy2 h_equal
    rw [←(hg y1 hy1).2, h_equal, (hg y2 hy2).2]

  -- Define a function θ that is basically the same as function g
  let θ (y : β) (_ht : y ∈ Y) := g y

  have aux1 :  ∀ (a : β) (ha : a ∈ Y), θ a ha ∈ X := fun y hy => (hg y hy).1

  have aux2 : ∀ (a₁ a₂ : β) (ha₁ : a₁ ∈ Y) (ha₂ : a₂ ∈ Y), θ a₁ ha₁ = θ a₂ ha₂ → a₁ = a₂
    := fun _ _ hy1 hy2 hk => g_inj hy1 hy2 hk

  have aux3 : X.card ≤ Y.card := Nat.le_of_eq h_card

  -- The function g is a surjection from Y to X
  have g_sur : SurjOn g Y X := by
    -- show ↑X ⊆ (g '' ↑Y)
    intro x hx
    simp
    -- show ∃ y  ∈ Y, g y = x
    obtain ⟨y, hy⟩ :=
      (Finset.surj_on_of_inj_on_of_card_le θ aux1 aux2 aux3 x) hx
    obtain ⟨hk1, hk2⟩ := hy
    exact ⟨y, hk1, hk2.symm⟩

  -- g is a bijection on Y
  have g_bij : BijOn g Y X := by
    constructor
    · -- Show that function g maps elements in Y to elements in X
      intro y hy
      exact (hg y hy).1
    · exact ⟨g_inj, g_sur⟩  -- g is injective and surjective

  -- g is a left/right inverse of f
  have LeftRight_inv : Set.InvOn g f X Y := by
    constructor
    · -- g is a left inverse of f
      dsimp [LeftInvOn]
      intro x hx
      obtain ⟨y', hy⟩ := g_sur hx
      -- y' is an element in Y such that x = g y'
      calc
        g (f x) = g (f (g y')) := by rw [hy.2]
            _ = g y' := by rw [(hg y' hy.1).2]
            _ = x := by rw [hy.2]
    · -- g is a right inverse of f
      intro y hy
      exact (hg y hy).2

  -- Because g is a bijection
  -- and g is the left/right inverse of f,
  -- => the function f is a bijection
  exact Set.BijOn.symm LeftRight_inv g_bij




-- There is no bijection from a finite set X to a proper subset of X.
--
-- Function f below is a bijection from X to a set Y, which is
-- a proper subset of X.
-- Show that such a function f does not exist.
example (X Y : Finset α)
  : ¬ ∃ f : α → α , BijOn f X Y  ∧  Y ⊂ X := by
  intro h
  obtain ⟨f , h_bij, h_proper_subset⟩ := h

 -- The cardinality of X and Y are equal
  have equal_cardinality : Y.card = X.card := by
    obtain ⟨h1,h2,h3⟩ := h_bij
    have hXY : X.card ≤ Y.card := by
      exact card_le_card_of_inj_on f h1 h2
    have hYX : Y.card ≤ X.card := by
      unfold Set.SurjOn at h3
      exact LE.le.trans (card_le_card (mod_cast h3)) card_image_le
    exact Nat.le_antisymm hYX hXY

  -- The cardinality of X and Y are not equal
  have not_equal_cardinality : Y.card ≠ X.card :=
     Nat.ne_of_lt (Finset.card_lt_card h_proper_subset)

  contradiction
