import Mathlib.Tactic

-- set_option autoImplicit true
set_option linter.style.emptyLine false
set_option linter.constructorNameAsVariable false

universe u v

class Cat (obj : Type u) where
  -- 1. Data
  /-- The type of morphisms from `X` to `Y` -/
  Hom : obj → obj → Type v

  /-- The identity morphism on an object `X` -/
  id : (X : obj) → Hom X X

  /-- Composition of morphisms. Note the diagrammatic order: f then g -/
  comp : {X Y Z : obj} → Hom X Y → Hom Y Z → Hom X Z

  -- 2. Axioms (Properties)
  /-- Left identity law: id ≫ f = f -/
  id_comp : ∀ {X Y : obj} (f : Hom X Y), comp (id X) f = f

  /-- Right identity law: f ≫ id = f -/
  comp_id : ∀ {X Y : obj} (f : Hom X Y), comp f (id Y) = f

  /-- Associativity of composition: (f ≫ g) ≫ h = f ≫ (g ≫ h) -/
  assoc : ∀ {W X Y Z : obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)




/-
 ## Example of a category containing only one object and an identity morphism
-/

inductive OneObj : Type u where
  | star

inductive OneMor : Type v where
  | unit

instance oneObjectOneMorphismCat : Cat.{u, v} OneObj where
  Hom := fun _ _ => OneMor
  id := fun _ => OneMor.unit
  comp := fun _ _ => OneMor.unit
  id_comp := by
    intro X Y f
    cases f
    rfl
  comp_id := by
    intro X Y f
    cases f
    rfl
  assoc := by
    intro W X Y Z f g h
    cases f
    cases g
    cases h
    rfl




/-
 ## A category with one object and two morphisms
    The first morphism is the identity.
    The non-identity morphism is an idempotent
-/

/-- A type with exactly two morphisms. -/
inductive TwoMor : Type v where
  | e   -- identity morphism
  | f   -- non-identity morphism

namespace TwoMor

/-- Composition table for the two morphisms.

The morphism `e` behaves as the identity, and `f ≫ f = f`.
-/
def comp : TwoMor → TwoMor → TwoMor
  | e, m => m
  | m, e => m
  | f, f => f

/-- The extra morphism `f` is not equal to the identity morphism `e`. -/
theorem f_ne_e : f ≠ e := by
  intro h
  cases h

end TwoMor

/-- The category with one object and two morphisms. -/
instance oneObjectTwoMorphismCat : Cat.{u, v} OneObj where
  Hom := fun _ _ => TwoMor

  id := fun _ => TwoMor.e

  comp := fun f g => TwoMor.comp f g

  id_comp := by
    intro X Y f
    cases f <;> rfl

  comp_id := by
    intro X Y f
    cases f <;> rfl

  assoc := by
    intro W X Y Z f g h
    cases f <;> cases g <;> cases h <;> rfl

-- The non-identity morphism is idempotent
-- In category theory, it says f ≫ f = f
theorem f_idempotent :
    TwoMor.comp TwoMor.f TwoMor.f = TwoMor.f := by
  rfl

-- Every morphism is idempotent
theorem every_morphism_idempotent (m : TwoMor) :
    TwoMor.comp m m = m := by
  cases m <;> rfl

-- The non-identity morphism is not the identity
theorem f_is_not_identity :
    TwoMor.f ≠ TwoMor.e := by
  intro h
  cases h

-- The morphism f has no inverse
theorem f_has_no_inverse :
    ¬ ∃ g : TwoMor,
      TwoMor.comp TwoMor.f g = TwoMor.e ∧
      TwoMor.comp g TwoMor.f = TwoMor.e := by
  intro h
  rcases h with ⟨g, hg₁, hg₂⟩
  cases g
  · cases hg₁
  · cases hg₁

-- The only invertible morphism is the identity
theorem only_identity_is_invertible
    (m : TwoMor)
    (h : ∃ g : TwoMor,
      TwoMor.comp m g = TwoMor.e ∧
      TwoMor.comp g m = TwoMor.e) :
    m = TwoMor.e := by
  cases m
  · rfl
  · exfalso
    apply f_has_no_inverse
    exact h

/- ### Summary
- f ≠ id
- f ≫ f = f
- every morphism is idempotent
- f is not invertible
- the only invertible morphism is the identity

Mathematically, this category is the one-object category
associated to the two-element monoid {e,f}
where
e * e = e
e * f = f
f * e = f
f * f = f
-/



/-
## The free category on one object and one generating endomorphism.

Morphisms are natural numbers:

* `0` is the identity morphism;
* `1` is the generator `f`;
* `2` is `f ≫ f`;
* `3` is `f ≫ f ≫ f`;
* etc.

Composition is addition.
-/

namespace FreeLoopCategory

/- The category has one object. -/
inductive Obj : Type where
  | star

instance : Cat Obj where
  Hom := fun _ _ => Nat -- morphisms are nonnegative integers
  id := fun _ => 0
  comp := fun f g => f + g

  id_comp := by
    intro X Y f
    exact Nat.zero_add f

  comp_id := by
    intro X Y f
    exact Nat.add_zero f

  assoc := by
    intro W X Y Z f g h
    exact Nat.add_assoc f g h

/-- The unique hom-type from `star` to `star`. -/
abbrev End : Type := Cat.Hom (obj := Obj) Obj.star Obj.star

/-- The generating morphism `f`. -/
def gen : End := (1 : Nat)

/-- The morphism corresponding to `f` composed with itself `n` times. -/
def loop (n : Nat) : End := n

/-- The identity morphism is `0`. -/
theorem id_eq_zero :
    (Cat.id (obj := Obj) Obj.star : End) = (0 : Nat) := by
  rfl

/-- Composition is addition. -/
theorem comp_eq_add (m n : End) :
    Cat.comp (obj := Obj)
      (X := Obj.star) (Y := Obj.star) (Z := Obj.star)
      m n
    =
    Nat.add (show Nat from m) (show Nat from n) := by
  rfl

theorem comp_eq_add' (m n : End) :
    Cat.comp (obj := Obj)
      (X := Obj.star) (Y := Obj.star) (Z := Obj.star)
      m n
    =
    ((show Nat from m) + (show Nat from n) : Nat) := by
  rfl


/-- The generator is not the identity. -/
theorem gen_eq_id :
    gen ≠ Cat.id (obj := Obj) Obj.star := by
  change (1 : Nat) ≠ 0
  decide

/-- The generator composed with itself is not the generator. -/
theorem gen_comp_gen_ne_gen :
    Cat.comp (obj := Obj) gen gen ≠ gen := by
  change ((1 : Nat) + 1) ≠ 1
  decide


/-- Composing powers of the generator corresponds to addition. -/
theorem loop_comp_loop (m n : Nat) :
    Cat.comp (loop m) (loop n) = loop (m + n) := by
  rfl

/--
There is no relation between powers of the generator except 
equality of exponents.

In other words, `f^m = f^n` implies `m = n`.
-/
theorem loop_injective :
    Function.Injective loop := by
  intro m n h
  simpa [loop] using h

/-- In particular, `f ≫ f` is not equal to `f`. -/
theorem gen_comp_gen_ne_gen' :
    Cat.comp gen gen ≠ gen := by
  change (1 + 1 : Nat) ≠ 1
  decide


/--
The generator has no inverse in the free one-loop category.
This reflects the fact that `ℕ` under addition is a monoid, not a group.
-/
theorem gen_has_no_inverse :
    ¬ ∃ g : End,
      Cat.comp (obj := Obj)
        (X := Obj.star) (Y := Obj.star) (Z := Obj.star)
        gen g
        =
      Cat.id (obj := Obj) Obj.star
      ∧
      Cat.comp (obj := Obj)
        (X := Obj.star) (Y := Obj.star) (Z := Obj.star)
        g gen
        =
      Cat.id (obj := Obj) Obj.star := by
  intro h
  rcases h with ⟨g, hg⟩
  rcases hg with ⟨hleft, hright⟩

  -- Since `gen = 1`, the equation `gen ≫ g = id`
  -- becomes `1 + g = 0`.
  change Nat.add 1 (show Nat from g) = 0 at hleft

  -- But `1 + g` is a successor, so it cannot be `0`.
  cases hright

end FreeLoopCategory





-- Example of category
-- hom sets are just functions between types
instance : Cat (Type u) where
  Hom X Y := X → Y
  id _X := fun x => x
  -- Diagrammatic composition: perform f first, then apply g
  comp f g := fun x => g (f x)

  -- The proofs for the axioms are trivially true by reflexivity in Lean
  id_comp _f := rfl
  comp_id _f := rfl
  assoc _f _g _h := rfl


/-
 The type `Cat` is custom made in this program. 

 In Mathlib, category is defined as
 instance : Category C where
  Hom X Y := ...
  id X := ...
  comp f g := ...
  id_comp := ...
  comp_id := ...
  assoc := ...

  Mathlib also defines some notation:
X ⟶ Y      -- Hom X Y
𝟙 X        -- identity morphism
f ≫ g      -- composition, diagrammatic order
-/

open CategoryTheory

-- Let C be an arbitrary category
variable {C : Type u} [Category C]

-- Let X, Y, Z be objects in C
variable {X Y Z : C}

-- f and g are morphisms. `⟶` (typed via \hom) is Mathlib notation for Hom
variable (f : X ⟶ Y) (g : Y ⟶ Z)

-- We can define a new morphism by composing f and g
-- `≫` (typed via \gg) is Mathlib notation for diagrammatic composition
def my_composition : X ⟶ Z := f ≫ g

-- `𝟙` (typed via \b1) is Mathlib notation for the identity morphism
def my_identity : X ⟶ X := 𝟙 X

-- We can prove basic theorems using Mathlib's built-in simp lemmas:
example : (𝟙 X ≫ f) ≫ 𝟙 Y = f := by
  simp -- `simp` automatically applies `id_comp` and `comp_id`

