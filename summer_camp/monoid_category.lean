/-
  Examples of defining monoid, preorder and category

Youtube source: Categories, Monoids, and Preorders (in Lean4)
-/

import Mathlib.Tactic

set_option autoImplicit true


namespace hidden

section monoid

/-
  Structure for defining a monoid.
  Type `M` is the underlying type of the monoid.
  `mul` is the binary operation of the monoid.
  `e` is the identity element of the monoid.
  `assoc` is the associativity property of the binary operation.
  `identity` is the identity property of the binary operation.
-/
structure Monoid M where
  mul : M → M → M
  e : M
  assoc : mul a ( mul b c) = mul ( mul a b) c
  identity : mul a e = a ∧ mul e a = a



/-
 Monoid of functions
-/
def Monoid.function : Monoid (α → α) where
  mul f g := f ∘ g
  e := fun x ↦ x
  assoc := by
    intro f g h
    rfl
  identity := by
    intro f
    constructor
    · rfl
    · rfl

/- opposite monoid
  It is basically the same monoid but
  with the order of multiplication reversed.
-/
def Monoid.op (mon : Monoid M) : Monoid M where
  mul a b := mon.mul b a
  e := mon.e
  assoc := by
    intro a b c
    rw [ mon.assoc]
  identity := by
    intro a
    constructor
    · exact mon.identity.2
    · exact mon.identity.1


/-
  Product monoid
-/
def Monoid.product (mon₁ : Monoid M₁) (mon₂ : Monoid M₂)
    : Monoid (M₁ × M₂) where
  mul x y  := ( mon₁.mul x.1 y.1, mon₂.mul x.2 y.2 )
  e := ( mon₁.e, mon₂.e )
  assoc := by
    intro a b c
    rw [ mon₁.assoc, mon₂.assoc ]
  identity := by
    intro a
    constructor
    · rw [ mon₁.identity.1, mon₂.identity.1 ]
    · rw [ mon₁.identity.2, mon₂.identity.2 ]

end monoid




section preorder

/-
  Structure for defining a preorder.
  Type `α` is the underlying type of the preorder.
  `leq` is the binary relation of the preorder.
  `trans` is the transitivity property of the binary relation.
  `reflex` is the reflexivity property of the binary relation.
-/
structure Preorder α where
  leq : α → α → Prop
  trans : leq a b → leq b c → leq a c
  reflex : leq a a

/-
  Preorder of natural numbers
-/
def Preorder.nat : Preorder Nat where
  leq x y := x ≤ y
  trans := by
    intro a b c a_leq_b b_leq_c
    omega
  reflex := by
    intro a
    omega

/-
  Opposite preorder
-/
def Preorder.op (pre : Preorder α) : Preorder α where
  leq a b := pre.leq b a
  trans a_leq_b b_leq_c := pre.trans b_leq_c a_leq_b
  reflex := pre.reflex

/-
  Product preorder
-/
def Preorder.product (pre₁ : Preorder P₁) (pre₂ : Preorder P₂)
  : Preorder (P₁ × P₂) where
  leq x y := pre₁.leq x.1 y.1 ∧ pre₂.leq x.2 y.2
  trans := by
    intro a b c a_leq_b b_leq_c
    constructor
    · exact pre₁.trans a_leq_b.1 b_leq_c.1
    · exact pre₂.trans a_leq_b.2 b_leq_c.2
  reflex := by
    intro a
    constructor
    · exact pre₁.reflex
    · exact pre₂.reflex

end preorder




section category

/-
  Data structure for defining a category.
  Type `obj` is the underlying type of the category.
  `hom o1 o2` is the type of morphisms between objects `o1` and `o2`.
  `compose` is the composition of morphisms.
  `reflex` is the identity morphism for an object.
  `assoc` is the associativity property of morphism composition.
  `identity` is the identity property of morphism composition.
-/
structure Category obj where
  hom : obj → obj → Type v
  compose : hom a b → hom b c → hom a c
  reflex : hom a a
  assoc : compose f (compose g h) = compose (compose f g) h
  identity : compose f reflex = f ∧ compose reflex f = f


/-
  Monoid as a category
-/
def Category.monoid (mon : Monoid m) : Category Unit where
  hom _ _ := m  -- the type of morphisms is the underlying type of the monoid
  compose := mon.mul
  reflex := mon.e
  assoc := mon.assoc
  identity := mon.identity

/-
  Leq structure
  `leq_proof` is a proof that `a ≤ b` in the preorder `pre`.
-/
structure Leq (pre : Preorder p) (a b : p) : Type where
   leq_proof : pre.leq a b


/-
  Preorder as a category
-/
def Category.preorder (pre : Preorder p) : Category p where
  hom a b := Leq pre a b  -- the type of morphisms is the leq structure
  compose f g := {leq_proof := pre.trans f.leq_proof g.leq_proof}
  reflex := {leq_proof := pre.reflex}
  assoc := by
    intro _ _ f _ g _ h
    rfl
  identity := by
    intro _ _ f
    constructor
    · rfl
    · rfl

/-
  opposite category
-/
def Category.op {obj} (cat : Category obj) : Category obj where
  hom a b := cat.hom b a
  compose f g := cat.compose g f
  reflex := cat.reflex
  assoc := by
    intro _ _ f _ g _ h
    rw [←  cat.assoc ]
  identity := by
    intro _ _ f
    constructor
    · exact cat.identity.2
    · exact cat.identity.1

/-
product category
-/
def Category.product {obj₁ obj₂} (cat₁ : Category obj₁) (cat₂ : Category obj₂)
  : Category (obj₁ × obj₂) where
  hom x y := cat₁.hom x.1 y.1 × cat₂.hom x.2 y.2
  compose f g := ( cat₁.compose f.1 g.1, cat₂.compose f.2 g.2 )
  reflex := ( cat₁.reflex, cat₂.reflex )
  assoc := by
    intro _ _ f _ g _ h
    rw [ cat₁.assoc, cat₂.assoc ]
  identity := by
    intro _ _ f
    constructor
    · rw [ cat₁.identity.1, cat₂.identity.1 ]
    · rw [ cat₁.identity.2, cat₂.identity.2 ]

/-
  The morphisms of this category are functions between two
  objects. Composition of function is the usual function composition.
-/
def Category.function : Category (Type v) where
  hom A B := A → B
  compose f g := g ∘ f
  reflex := fun x ↦ x
  assoc := by
    intro _ _ f _ g _ h
    rfl
  identity := by
    intro _ _ f
    constructor
    · rfl
    · rfl



end category

end hidden
