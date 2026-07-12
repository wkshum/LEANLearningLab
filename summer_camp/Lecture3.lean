import Mathlib.Data.Real.Basic
import Mathlib.Tactic


-- for all ∀ is like function application

namespace hidden

example (f : ℕ→ℕ) (h : ∀ x:ℕ, f x = 2*x)
   : f 1 = 2 := by
  exact h 1

example (x:ℕ) : x^2 = x*x := by
  exact Nat.pow_two x

example : ∀ x:ℕ, x^2=x*x := by
  intro a
  exact Nat.pow_two a

example {n:ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
  exact Nat.eq_one_of_dvd_one (hn 1)



-- Definition of injective, surjective, bijective

def Injective (f:A→B) := ∀ a b: A, f a = f b → a = b

def Surjective (g: A→B) := ∀ b : B , ∃ a:A , g a = b

def Bijective (h:A→B) := Injective h ∧ Surjective h

-- example of linear function

def F1 (x:ℝ)  := x*2 + 1


-- prove that F1 is injective
example : Injective F1 := by
  unfold Injective
  intro x y
  intro h
  dsimp only [F1] at h
  linarith [h]

-- Prove that F1 is surjective
example : Surjective F1 := by
  unfold Surjective
  intro y
  use (y-1)/2
  dsimp [F1]
  linarith

-- Prove that F1 is bijective
example : Bijective F1 := by
  unfold Bijective
  constructor
  · intro x y
    intro h
    dsimp only [F1] at h
    linarith [h]
  · intro y
    use (y-1)/2
    dsimp [F1]
    linarith


def F2 (x:ℝ) := x^2

-- Prove that the square function is not injective
example : ¬ Injective F2 := by
  dsimp [Injective]
  push_neg
  use -1, 1
  constructor
  · dsimp [F2]
    norm_num
  · norm_num

-- Prove that the square function is not surjective
example : ¬ Surjective F2 := by
  dsimp [Surjective]
  push_neg
  use -1
  intro x
  apply ne_of_gt
  have h2 : (-1:ℝ) < 0 := by exact neg_one_lt_zero
  have h3 : 0≤x^2 := by exact sq_nonneg x
  exact gt_of_ge_of_gt h3 h2



-- Relation between bijective, injective and surjective

-- If a function is bijective, then it is injective
lemma bij_inj {X Y: Type*} (f: X→ Y) (h : Bijective f) : Injective f := by
  obtain ⟨ h1 , _ ⟩ := h
  exact h1

-- If a function is bijective, then it is surjective
lemma bij_sur {X Y: Type*} (f: X→ Y) (h : Bijective f) : Surjective f := by
  obtain ⟨ _ , h2 ⟩ := h
  exact h2

-- If a function is injective and bijective, then it is bijective
lemma inj_sur_bij {X Y : Type*} (f:X→Y) (h1: Injective f) (h2: Surjective f) : Bijective f :=
  And.intro h1 h2




/-
  Set

  Set α is implemented α → Prop

  If A has type Set α, x ∈ A is implemented as A x

  {x | P x} is represented by fun x ↦ P x

  y ∈ {x | P x} is the same P y
-/

#check {n:ℤ | n ≥ 1}

#check 0 ∈ {n:ℤ | n ≥ 1}


-- Prove that 4 belongs to the set of the set of even integers
example : 4 ∈ {n:ℤ | 2 ∣ n} := by
  dsimp
  dsimp [Dvd.dvd]
  use 2
  norm_num


-- Prove that 1 does not belong to the set of even integers
example : 1 ∉ { n:ℤ | 2 ∣ n} := by
  dsimp
  dsimp [Dvd.dvd]
  intro h
  obtain ⟨k, hk⟩ := h
  obtain h1 | h2  := le_or_lt k 0
  -- divide into two cases
  -- In both cases, prove that there is a contradiction
  · -- k ≤ 0
    have h3 : (1:ℤ)≤ 0 :=
      calc
        1 = 2*k := by rw [hk]
         _≤ 2*0 := by rel [h1]
    exact (Int.negSucc_not_nonneg 0).mp h3
  · -- case k>0
    have h4 : k≥ 1 := by exact h2
    have : (1:ℤ) ≥ 2 :=
      calc
        1 = 2*k := hk
        _ ≥ 2*1 := by rel [h4]
    norm_num at this


-- Prove that 3 does not divide 7
example : ¬ (3:ℤ) ∣ 7 := by
  apply (Int.exists_lt_and_lt_iff_not_dvd 7 ?_).mp
  · use 2
    constructor <;> norm_num
  norm_num


-- Union of set is the same as logic OR of two propositions
example : 13 ∈ {n:ℤ | 7∣n} ∪ {n:ℤ | n ≥ 10} := by
  right
  norm_num


-- Examples from MIL about set inclusions

variable (s t u : Set α)

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

open Set
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def]
  rw [subset_def] at h
  rw [inter_def, inter_def]
  simp only [mem_setOf]
  intro x
  intro ⟨xs, xu⟩
  exact ⟨h x xs, xu⟩



end hidden
