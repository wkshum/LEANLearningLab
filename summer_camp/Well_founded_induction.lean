import Mathlib.Tactic

/-

 Well-founded induction

 In systems like ZFC Set Theory, well-foundedness is just a
 property of sets used to avoid paradoxes (like the Axiom of Foundation).
 In Lean (and dependent type theory in general), well-foundedness is
 a computational data structure (Acc) that the compiler manipulates to
 guarantee program safety, prove the consistency of the logic, and
 safely compile high-level math down to optimized C code.

 As a result, well-foundedness is built directly into the core of Lean.
-/

open Classical

#print WellFounded

/-- the definition of WellFounded in Lean
  `r` is a relation on type `α`
  a type `α` is well-founded iff all term `a` in `A` is accessible
  with respect to the relation `r`.
-/
inductive WellFounded'.{u} : {α : Sort u} → (α → α → Prop) → Prop
  | apply {α : Sort u} {r : α → α → Prop} :
      (∀ (a : α), Acc r a) → WellFounded' r

#print Acc

-- accessible term x
inductive Acc'.{u} : {α : Sort u} → (α → α → Prop) → α → Prop
  | intro  {α : Sort u} {r : α → α → Prop} (x : α) :
      (∀ (y : α), r y x → Acc r y) → Acc' r x

/-- 1. Well-founded induction
    Lean provides `WellFounded.induction` natively, but we can
    recreate our specific version for the `<` relation to show
    how it hooks into Lean's structure.
-/
theorem custom_wellFounded_induction {A : Type} [LT A]
  (wf : WellFounded (fun a b : A => a < b)) {P : A → Prop}
  (h : ∀ a : A, (∀ b : A, b < a → P b) → P a)
  (a : A) : P a := by
  -- `wf` is a structure containing `apply : ∀ a, Acc r a`.
  have ⟨apply⟩  := wf
  have h_acc := apply a
  -- We do induction on the accessibility of `a`

  induction h_acc with
  | intro x _ ih => exact h x ih

/-- 2. Noetherian ring
    We can define Noetherian ring in terms of well-foundedness.
-/
def IsNoetherian_custom (R : Type) [Ring R] : Prop :=
  WellFounded (fun (a b : Ideal R) => a > b)


/-- 3. Well-foundedness ↔ No infinite descending sequences
    Adapted to use Lean's `Acc (fun x y => x < y)`.
-/
theorem acc_iff_no_decreasing_seq' {A : Type} [LT A] (a : A) :
    Acc (fun x y => x < y) a ↔ ¬ ∃ f : ℕ → A, (∀ n : ℕ, f (n + 1) < f n) ∧ f 0 = a := by
  constructor
  · -- Forward direction
    intro h
    suffices ∀ f : ℕ → A, (∀ n, f (n + 1) < f n) → f 0 ≠ a by
      intro ⟨f, h1, h2⟩
      exact this f h1 h2
    -- Induct on the accessibility of `a`
    induction h with
    | intro x _ ih =>
      intro f hf ha
      let f' n := f (n + 1)
      have hf' : ∀ n, f' (n + 1) < f' n := fun n => hf (n + 1)
      let b := f' 0
      have hba : b < x := ha ▸ hf 0
      exact ih b hba f' hf' rfl

  · -- Backward direction
    intro ha
    by_contra h_not_acc
    -- Create the subset of inaccessible elements
    let InAcc := { x : A // ¬ Acc (fun x y => x < y) x }

    -- Prove that every inaccessible element has an inaccessible element smaller than it
    have H_step : ∀ x : InAcc, ∃ y : InAcc, y.val < x.val := by
      intro ⟨x, hx⟩
      by_contra h_no_smaller
      push Not at h_no_smaller  -- Automatically turns `¬∃` into `∀... ¬...`
      have h_acc_x : Acc (fun x y => x < y) x := by
        constructor
        intro y hyx
        by_contra hy_inacc
        exact h_no_smaller ⟨y, hy_inacc⟩ hyx
      exact hx h_acc_x

    -- Use the Axiom of Choice to pick the next step
    let f_next : InAcc → InAcc := fun x => Classical.choose (H_step x)
    have h_next : ∀ x : InAcc, (f_next x).val < x.val := fun x => Classical.choose_spec (H_step x)

    -- Construct the infinite sequence recursively
    let x0 : InAcc := ⟨a, h_not_acc⟩
    let f_seq : ℕ → InAcc := fun n => Nat.recOn n x0 (fun _ prev => f_next prev)

    have ha_ex : ∃ f : ℕ → A, (∀ n, f (n + 1) < f n) ∧ f 0 = a := by
      use fun n => (f_seq n).val
      constructor
      · intro n
        exact h_next (f_seq n)
      · rfl
    exact ha ha_ex


/-- 4. Well-foundedness ↔ Minimal elements in non-empty subsets
    Notice how clean this becomes using standard `Acc` and Mathlib's `push_neg`!
-/
theorem wellFounded_iff_has_minimal {A : Type} [LT A] :
  WellFounded (fun a b : A => a < b) ↔
  ∀ (S : A → Prop), (∃ x, S x) → ∃ m, S m ∧ ∀ y, S y → ¬(y < m) := by
  constructor
  · -- Forward direction
    intro wf S ⟨x, hx⟩
    by_contra h
    push Not at h -- push negative `¬∃ m...` into `∀ m, S m → ∃ y, S y ∧ y < m`

    have h_empty : ∀ a, ¬ S a := by
      intro a
      have ⟨h_apply⟩ := wf
      have h_acc := h_apply a
      induction h_acc with
      | intro b _ ih =>
        intro hb
        have ⟨y, hy_S, hy_lt⟩ := h b hb
        exact ih y hy_lt hy_S

    exact h_empty x hx

  · -- Backward direction
    intro H
    constructor
    intro a
    by_contra h_not_acc

    let S := fun x => ¬ Acc (fun a b : A => a < b) x
    have hEx : ∃ x, S x := ⟨a, h_not_acc⟩

    have ⟨m, hm, hmin⟩ := H S hEx

    have h_acc_m : Acc (fun a b : A => a < b) m := by
      constructor
      intro y hym
      by_contra hy_not_acc
      exact hmin y hy_not_acc hym

    exact hm h_acc_m


/-- 5. Irreflexivity (No self-loops) -/
theorem wf_irrefl {A : Type} {r : A → A → Prop}
  (wf : WellFounded r) (x : A) : ¬ r x x := by
  have ⟨h_apply⟩ := wf
  have h_acc := h_apply x
  -- Induct on the accessibility of x
  induction h_acc with
  | intro a _ ih =>
    intro h
    -- The induction hypothesis `ih` says that for any `y < a`, `¬ (y < y)`.
    -- By setting `y = a`, we immediately get a contradiction.
    exact ih a h h
