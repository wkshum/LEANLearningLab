import Mathlib.Tactic

open Function

-- Sum type

inductive College : Type where
  | Muse : College
  | Ling : College
  | Shaw : College
deriving Repr, DecidableEq

#check College



open College

def a : College := Shaw

#check a
#eval a

def F (x:College) : College :=
 match x with
 | Muse => Shaw
 | Ling => Shaw
 | Shaw => Ling

example : ¬ Surjective F := by
  dsimp [Surjective]
  push_neg
  use Muse
  intro x
  cases x <;> trivial

example : ¬ Injective F := by
  dsimp [Injective]
  push_neg
  use Muse, Ling
  constructor
  · rfl
  · trivial


 def G (x:College) : College :=
 match x with
 | Muse => Ling
 | Ling => Shaw
 | Shaw => Muse

example : Surjective G := by
  dsimp [Surjective]
  intro x
  match x with
  | Muse => use Shaw ; rfl
  | Ling => use Muse ; rfl
  | Shaw => use Ling ; rfl

example : Injective G := by
  dsimp [Injective]
  intro x y
  intro h
  cases x <;>  cases y <;> trivial


 def H := G ∘ G ∘ G

#eval H Muse
#eval H Ling
#eval H Shaw

def id' (x:College) : College :=
 match x with
 | Muse => Muse
 | Ling => Ling
 | Shaw => Shaw

example : H = id' := by
  ext x
  cases x <;> rfl


-- Product type
@[ext]
structure Point where
 x: ℚ
 y: ℚ
 z: ℚ

-- Display a variable of type Point
unsafe instance instRepr : Repr Point where
  reprPrec P _  :=
    "("++reprPrec P.x 20 ++ " , " ++ reprPrec P.y 20 ++ " , " ++ reprPrec P.z 20 ++")"


def P1 : Point :=
 { x:=1, y:= 2, z:= -1}

def P2 := Point.mk 1 2 3

#check P2
#eval P2
#check Point

def P3 : Point := ⟨1,3,5⟩

def P4 : Point where
  x := 3
  y := 5
  z := 10

example (p q : Point)
 (hx : p.x = q.x)
 (hy : p.y = q.y)
 (hz : p.z = q.z)
: p = q := by
 ext
 repeat assumption

def add (p q : Point) : Point :=
  ⟨ p.x + q.x , p.y + q.y, p.z + q.z⟩

#check add P1 P2
#eval add P1 P2


-- Prove that 11 is congruent to 3 mod 4
example : 11 ≡ 3 [ZMOD 4] := by
  apply Int.modEq_of_dvd  -- convert to the more mathematical definition of modulo
  use -2
  norm_num

-- Prove that if a≡b mod n and c≡d mod n
-- then a+c ≡ b+d mod n
theorem test {n a b c d : ℤ}
(h1 : a ≡ b [ZMOD n])
(h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  apply Int.ModEq.dvd at h1
  apply Int.ModEq.dvd at h2
  apply Int.modEq_of_dvd
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    b+d-(a+c)= (b-a) + (d-c) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

