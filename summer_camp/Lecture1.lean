import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-
 Function
-/

def f (x y: ℤ) : ℤ := 2*x+3*y

def g := fun x : ℤ => 2*x + 6

def h := (f · 2)  -- fix y to 2, and let x be the variable

-- prove that function g is the same as function h
example : g = h := by
  ext x
  rw [g, h , f]
  ring

/-
  Product type
-/

def create_product (a b: ℕ) : ℕ×ℕ  := (a,b)

#eval create_product 4 5

def p := create_product 3 4

#eval p
#eval p.1
#eval p.2

/-
  Proposition
-/

-- Propositions
#check True   -- has a unique element called "trivial"
#check False  -- False is always empty

-- elements in Bool
#check true
#check false

#check trivial

/-
 Logical AND
-/

-- elimination of AND
example (h : A∧B) : A := h.1
example (h : A∧B) : B := h.2

-- introduction of AND

example (h1 : A) (h2: B) : A∧B :=
 ⟨h1, h2⟩

-- AND is commutative, term mode
example (h : A∧B) : B∧A :=
  ⟨ h.2, h.1⟩

 -- AND is commutative, tactic mode
example (h : A∧B) : B∧A  := by
  obtain ⟨ha,hb⟩ := h
  constructor
  · exact hb
  · exact ha

example : True := trivial

-- Tactic mode
example (h : False) : A :=
  by exact h.elim

-- term mode
example (h : False) : 2 =3 := h.elim

/- Logical OR -/
example (ha : A) : A∨B := by
  exact Or.intro_left B ha

example (ha : B) : A∨B := by
  exact Or.inr ha

-- prove that if x=1 or y=-1, then xy+x=y+1
example (x y : ℝ) (h : x=1 ∨ y=-1) :
  x*y+x= y+1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1* y + 1 := by rw [hx]
            _ = y + 1 := by ring
  calc
    x * y + x = x * (-1) + x := by rw [hy]
            _ = (-1) + 1 := by ring
            _ = y+1 := by rw [hy]

/- Existential quantifier -/

-- There exists an integer that is
--  strictly larger than 3
example  : ∃ (x :ℤ ) , x > 3 := by
  use 4
  linarith

-- IF a = b^2 + 1 for some b, then a > 0
example (a : ℚ) (h : ∃ b : ℚ , a = b^2 + 1)
  : a > 0 := by
--  obtain ⟨b , hb⟩ := h
  rcases h with ⟨b, hb⟩
  calc
    a = b^2 + 1 := hb
    _ > 0  := by positivity

  /-
  Negation
  ¬ A := A → False
  -/

-- P and not P implies False,  term mode
-- ¬ p is the same as p implies False
example (p : Prop) (h1 : p) (h2 : ¬ p) : False := by
  contradiction


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

-- An example from Mechanics of Proof
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
