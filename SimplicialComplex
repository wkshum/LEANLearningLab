import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Slice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Order

open Classical
open BigOperators

/-
Examples from Loh's "Exploring formalization"
-/

/-!
# Section 3.2 Simplicial complexes
-/

-- The property that a family of sets is closed under
-- taking subsets
@[simp]
def is_subset_closed {a : Type*} (S: Set (Finset a)) :=
  ∀ s ∈ S, ∀ t, t ⊆ s → t ∈ S


/--
Simplicial complex consists of a set of subsets, and satisfies
the axiom that it is closed under going downward
-/
structure simplicial_complex (a : Type*) where
  simplices : Set (Finset a)
  subset_closed : is_subset_closed simplices


/--
 `vertices` is a set consisting of all vertices that appear in the simplicial complex
-/
def vertices {a : Type*} (X : simplicial_complex a) : Set a :=
{x : a | ∃ s ∈ X.simplices , x∈ s}

-- Empty simplicial complex
def empty_sc {α :Type*} : (simplicial_complex α) :=
  simplicial_complex.mk (∅ : Finset (Finset α)) (by tauto)



-- the simplex with vertex set V
@[simp]
def simplex {α : Type*} (V: Finset α) : (simplicial_complex α) where
  simplices := Finset.powerset V
  subset_closed := by
    dsimp
    simp
    tauto

-- The standard simplex with vertex set {0,1,2,... n}
@[simp]
def std_simplex (n:ℕ) : (simplicial_complex ℕ) := simplex (Finset.range (n+1))


-- Define the dimension of a finite set s as one less the cardinality
@[simp]
def dim {α  :Type*} (s : Finset α) : ℤ :=
  Finset.card s - 1


--#eval dim (Finset.range 5)   -- 4
--#eval dim (Finset.range 0)   -- -1



-- Dimension of a simplicial complex `X` is less than or equal to `n`
-- if all simplices in `X` is less than or equal to `n`
@[simp]
def has_dimension_leq {α : Type*} (X : simplicial_complex α) (n:ℕ) :=
  ∀ s ∈ X.simplices, dim s ≤ n

-- Dimension of a simplicial comlex `X` is larger than `n`
-- if there is one simplices in `X` that is larger than `n`
@[simp]
def has_dimension_geq {α : Type*} (X : simplicial_complex α) (n:ℕ) :=
  ∃ s ∈ X.simplices, dim s ≥ n

-- Definition of the dimension of a simplicial complex
@[simp]
def has_dimension {α : Type*} (X : simplicial_complex α) (n:ℕ) :=
 has_dimension_leq X n ∧ has_dimension_geq X n



-- -- Dimension of the standard simplex
-- lemma dim_std_simplex (n:ℕ) : has_dimension (std_simplex n) n :=
--   sorry


/-
Section 3.3 Simplicial maps

todo
-/



/-!
# Section 3.4 Finite simplicial complexes
-/


def is_finite_simplicial_complex {α : Type*} (X: simplicial_complex α) :=
  Set.Finite (X.simplices)


-- lemma fin_simplices_fin_vertices
--   {α : Type*}
--   (X : simplicial_complex α)
--   (X_fin_S : is_finite_simplicial_complex X)
--  :  Set.Finite (vertices X)
--  := sorry

-- lemma fin_vertices_fin_simplices
--   {α : Type*}
--   (X : simplicial_complex α)
--   (X_vin_V: Set.Finite (vertices X))
-- : is_finite_simplicial_complex X := sorry


-- Finite simplicial complex

structure fin_simplicial_complex (α : Type*) where
  simplices : Finset (Finset α)   -- simplices are finite sets
  subset_closed : is_subset_closed (simplices : Set (Finset α))

-- Convert from a finite simplicial complex to a simplicial complex
def to_sc
    {α : Type*}
    (X : fin_simplicial_complex α)
  : simplicial_complex α :=
    simplicial_complex.mk
      (↑ X.simplices)
      (X.subset_closed)


-- Coersion from finite simplicial complex to simplicial complex
instance  {α : Type*} : Coe (fin_simplicial_complex α) (simplicial_complex α) where
   coe := to_sc

-- Finite simplicial complex is finite
lemma fin_sc_is_finite {α : Type*} (X : fin_simplicial_complex α) :
  is_finite_simplicial_complex (↑X : simplicial_complex α) := by
    exact Finset.finite_toSet X.simplices




-- noncomputable
-- def to_fin_sc {α : Type*} (X : simplicial_complex α)
--   (fin_X : is_finite_simplicial_complex X)
--   : fin_simplicial_complex α :=
--   sorry




/-
# Section 3.5 Generating Simplicial Complexes

Examples of finite simplicial complexes
-/


-- Finitely generated simplices
@[simp]
def fingen_simplices
  {α : Type*}
  [DecidableEq α]
  (S : Finset (Finset α))
    : Finset (Finset α)
  :=  Finset.biUnion S (λ x => Finset.powerset x)



-- finitely generated simplices is subset closed
lemma fingen_simplices_sub_closed
  {α : Type*} [DecidableEq α]  (S : Finset (Finset α))  :
      is_subset_closed (↑(fingen_simplices S)  : Set (Finset α )) := by
  simp
  intro s x
  intro h_x_in_S
  intro h_s_in_x
  intro t
  intro h_t_in_s
  use x
  constructor
  · exact h_x_in_S
  · exact fun ⦃_⦄ t ↦ h_s_in_x (h_t_in_s t)

-- Finitely generated simplicial complex
-- Input a finite set S of finite sets
-- generate the corresponding simplicial complex that is subset closed
def fingen_simplicial_complex
  {α  : Type*} [DecidableEq α ]
  (S : Finset (Finset α ))
  : fin_simplicial_complex α where
      simplices := fingen_simplices S
      subset_closed := fingen_simplices_sub_closed S


-- Slice of a simplices by dimension
def simplices_of_dim {α : Type*} (X : fin_simplicial_complex α)
 (n : ℕ) : Finset (Finset α)
   := X.simplices.slice (n+1)


-- The example of cylinder
def cylinder : fin_simplicial_complex ℕ
  := fingen_simplicial_complex { {0,1,4}, {0,3,4}, {1,2,5}, {1,4,5}, {2,3,0}, {2,5,3} }


--#eval simplices_of_dim cylinder 0
--#eval simplices_of_dim cylinder 1
--#eval simplices_of_dim cylinder 2



-- The moebius strip
def moebius : fin_simplicial_complex ℕ :=
  fingen_simplicial_complex ({ {0,1,4}, {0,3,4}, {1,2,5}, {1,4,5}, {2,3,0}, {2,5,0} })


-- #eval simplices_of_dim moebius 0
-- #eval simplices_of_dim moebius 1
-- #eval simplices_of_dim moebius 2


-- The projective plane
def projective_plane : fin_simplicial_complex ℕ
:= fingen_simplicial_complex
{ {0,1,5}, {0,4,5}, {1,2,6}, {1,5,6}, {2,3,6}, {3,6,7}
, {4,5,8}, {4,7,8}, {5,6,9}, {5,8,9}, {6,7,4}, {6,4,9}
, {7,8,2}, {7,3,2}, {8,9,1}, {8,2,1}, {9,4,0}, {9,1,0} }

-- Octahedron as a simplicial complex
def octahedron : fin_simplicial_complex ℕ
:= fingen_simplicial_complex
{ {0,1,5}, {0,1,4}
, {1,2,5}, {1,2,4}
, {2,3,5}, {2,3,4}
, {3,0,5}, {3,0,4} }


def torus : fin_simplicial_complex ℕ
:= fingen_simplicial_complex
{ {0,1,4}, {0,3,4}, {1,2,5}, {1,4,5}, {2,0,3}, {2,5,3}
, {3,4,7}, {3,6,7}, {4,5,8}, {4,7,8}, {5,3,6}, {5,8,6}
, {6,7,1}, {6,0,1}, {7,8,2}, {7,1,2}, {8,6,0}, {8,2,0} }


def klein_bottle
: fin_simplicial_complex ℕ
:= fingen_simplicial_complex
{ {0,1,4}, {0,3,4}, {1,2,5}, {1,4,5}, {2,0,6}, {2,5,6}
, {3,4,7}, {3,6,7}, {4,5,8}, {4,7,8}, {5,3,6}, {5,8,3}
, {6,7,1}, {6,0,1}, {7,8,2}, {7,1,2}, {8,3,0}, {8,2,0} }



-- n dimensional sphere consists of all proper subsets of [0,1,...,n+1]
def sphere (n : ℕ) : fin_simplicial_complex ℕ
  := fingen_simplicial_complex
    (Finset.ssubsets (Finset.range (n+2)))

-- #eval simplices_of_dim (sphere 3) 1

-- #eval Finset.card (simplices_of_dim projective_plane 1)


/-!

# Section 3.6 Combining Simplicial complexes

-/



-- Union of simplicial complex is subset closed
lemma union_is_subset_closed
  {α : Type*} [DecidableEq α]
  (S : Finset (Finset α)) (T: Finset (Finset α))
  (S_sub_closed : is_subset_closed (S : Set (Finset α)))
  (T_sub_closed : is_subset_closed (T : Set (Finset α)))
  : is_subset_closed (↑(S ∪ T) : Set (Finset α)) := by
   sorry


-- Intersection of simplicial complex is subset closed
lemma inter_is_subset_closed
  {α : Type*} [DecidableEq α]
  (S : Finset (Finset α)) (T: Finset (Finset α))
  (S_sub_closed : is_subset_closed (S : Set (Finset α)))
  (T_sub_closed : is_subset_closed (T : Set (Finset α)))
  : is_subset_closed (↑(S ∩ T) : Set (Finset α)) := by
   sorry


-- The union of two simplicial complexes
def union_sc
  {α : Type*} [DecidableEq α]
  (X : fin_simplicial_complex α) (Y : fin_simplicial_complex α)
  : fin_simplicial_complex α  where
    simplices := X.simplices ∪ Y.simplices
    subset_closed := by
      exact union_is_subset_closed X.simplices Y.simplices X.subset_closed Y.subset_closed


-- Intersection of two simplicial complexes
def inter_sc
  {α : Type*} [DecidableEq α]
  (X : fin_simplicial_complex α) (Y : fin_simplicial_complex α)
  : fin_simplicial_complex α  where
    simplices := X.simplices ∩ Y.simplices
    subset_closed := by
      exact inter_is_subset_closed X.simplices Y.simplices X.subset_closed Y.subset_closed





-- Preparation for the zigzag complex
def zig (n :ℕ) : fin_simplicial_complex (ℕ × ℕ) :=
  fingen_simplicial_complex
   {{(n,0), (n+1,0)}, {(n,0), (n,1)}, {(n,1), (n+1,0)} }

-- Define the zigzag complex recursively
def zigzag : ℕ → fin_simplicial_complex (ℕ × ℕ)
  | 0    => fingen_simplicial_complex {{(0,0)}}
  | n+1  => union_sc (zigzag n) (zig n)



/-
 # Section 3.7 The Euler characteristic
-/


-- truncated parity function
def parity (x: ℤ) : ℤ :=
  if x < 0 then 0
  else if Int.mod x 2 = 0 then 1 else -1

def euler_char {α : Type*} (X : fin_simplicial_complex α) : ℤ :=
  ∑ s in X.simplices, parity (dim s)

notation "χ" => euler_char

-- #eval χ cylinder -- 0
-- #eval χ moebius -- 0
-- #eval χ projective_plane -- 1
-- #eval χ (sphere 5)



-- Prove that the Euler characteristic of a 2-sphere is 2
lemma euler_char_sphere_2 : χ (sphere 2) = 2 := by
  exact rfl


-- The Euler characteristic of the union of two simplicial complexes
theorem euler_char_union {α : Type*}
  (X : fin_simplicial_complex α)
  (Y : fin_simplicial_complex α)
: χ (union_sc X Y) = χ X + χ Y - χ (inter_sc X Y) := by
  calc
    χ (union_sc X Y)
      = ∑ s in (X.simplices ∪ Y.simplices), parity (dim s) := by rfl
    _ = (∑ s in (X.simplices ∪ Y.simplices), parity (dim s)
       + ∑ s in (X.simplices ∩ Y.simplices), parity (dim s))
       - ∑ s in (X.simplices ∩ Y.simplices), parity (dim s) := by ring
    _ = (∑ s in X.simplices, parity (dim s) + ∑ s in Y.simplices, parity (dim s) )
       - ∑ s in (X.simplices ∩ Y.simplices), parity (dim s) := by rw [Finset.sum_union_inter]
    _ = χ X + χ Y - χ (inter_sc X Y) := by rfl
  done

