import Mathlib.Tactic


section barber
-- Barber paradox

variable (men : Type)  -- men is a type
variable (barber : men)  -- barber is one of the men
variable (shaves : men → men → Prop) -- `shave x y` means x shaves y

example (h : ∀ x : men , shaves barber x ↔ ¬ shaves x x) : False := by
 -- consider two cases
 -- in each case we want to prove False
  by_cases hb : shaves barber barber
  · -- barber shaves himself
    have barber_doesnot_shaves_himself := (h barber).mp hb
    contradiction
  · -- barber does no shave himself
    have barber_shaves_himself := (h barber).mpr hb
    contradiction

-- shorter proof
example (h : ∀ x : men , shaves barber x ↔ ¬ shaves x x) : False := by
 -- consider two cases
 -- in each case we want to prove False
  by_cases hb : shaves barber barber
  · -- barber shaves himself
    exact absurd hb ( (h barber).mp hb)
  · -- barber does no shave himself
    exact absurd ((h barber).mpr hb) hb

end barber





section drinker
-- Drinker's paradox from the LEAN game Robo
-- Define a type People that the people in a bar
-- `Drinker x` means x drinks wine
-- Prove that if there is a person that drinks,
--    then all people in the bar drink.

theorem DrinkerParadox {People : Type} [h_nonempty : Nonempty People]
  (isDrinking : People → Prop) :
    ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  by_cases h : ∀ (y:People), isDrinking y
  · -- Suppose all people are drinkers
    rcases h_nonempty with ⟨z⟩  -- there exists a person z
    use z
    intro _h1
    assumption
  · -- Suppose not all people are drinkers
    push Not at h    -- push_neg in earlier versino of Mathlib
    obtain ⟨y, hy⟩ := h   -- there exists a non-Drinker y
    use y
    intro h1
    contradiction


end drinker





section Cantor

open Function

/-
  Cantor diagonal argument from Robo game
-/

/-
If we have a surjective function f : A → (A → Y),
then every function s : Y → Y has a fixed point.
-/
theorem cantor_diagonal_isFixedPt
 {A Y : Type} {f : A → A → Y} {s : Y → Y} (c : A → Y)
 (c_def : ∀ a, c a = s (f a a)) {b : A} (hb : f b = c)
 : Function.IsFixedPt s (f b b) := by
  unfold Function.IsFixedPt
  rw [← c_def]
  rw [hb]

theorem cantor_diagonal {A Y : Type} (f : A → A → Y)
   (hsurj : Function.Surjective f) (s : Y → Y)
    : ∃ x, Function.IsFixedPt s x := by
  let c : A → Y := fun (a : A) ↦ s (f a a)
  obtain ⟨a,ha⟩ := hsurj c
  use (f a a)
  apply cantor_diagonal_isFixedPt c
  · --
    exact fun a ↦ rfl
  · assumption

example (f : ℕ → ℕ → ℕ) :
  ∃ (g : ℕ → ℕ), ∀ (n : ℕ), f n ≠ g := by
  have h : ¬ Function.Surjective f := by
    intro h
    apply cantor_diagonal at h
    specialize h Nat.succ
    obtain ⟨n, hn⟩ := h
    dsimp [Function.IsFixedPt] at hn
    simp only [Nat.succ_ne_self] at hn
  unfold Function.Surjective at h
  push Not at h   -- push negative
  assumption

end Cantor
