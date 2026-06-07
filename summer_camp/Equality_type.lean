namespace LectureEquality

/-
Content:

1. Equality type in Lean.

2. A glimsp of equality in homotopy type theory, where equality
   is regarded as a path.
-/

/- 1. The Definition of Equality -/

inductive Eq {A : Type} : A → A → Prop
  | refl (a : A) : Eq a a


/- 2. Equivalence Relation Properties -/

-- Symmetry: If a = b, then b = a
theorem Eq.symm {A : Type} {a b : A} (h : Eq a b) : Eq b a := by
  induction h with
  | refl =>
    -- Because h was made by `refl`, Lean replaces `b` with `a`.
    -- The goal `Eq b a` becomes `Eq a a`.
    exact Eq.refl a

-- Transitivity: If a = b and b = c, then a = c
theorem Eq.trans {A : Type} {a b c : A} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c := by
  -- We do induction on h₂. This forces `c` to become `b`.
  -- The goal `Eq a c` becomes `Eq a b`, which is exactly h₁!
  induction h₂ with
  | refl => exact h₁


/- 3. NEW EXAMPLES: Congruence and Substitution -/

/-
Congruence (Applying a function to both sides)
If `a = b`, then `f a = f b`.
In math, this proves that functions are "well-defined".
-/
theorem Eq.congrArg {A B : Type} {a b : A}
  (f : A → B) (h : Eq a b) : Eq (f a) (f b) := by
  induction h with
  | refl =>
    -- By induction on `h`, `b` becomes `a`.
    -- The goal `Eq (f a) (f b)` becomes `Eq (f a) (f a)`.
    exact Eq.refl (f a)


/-
Substitution (Leibniz Equality)
If `a = b`, and some property `P` holds for `a`, it must hold for `b`.
This is the principle behind the `rw` (rewrite) tactic!
-/
theorem Eq.subst {A : Type} {a b : A}
  (P : A → Prop) (h : Eq a b) (ha : P a) : P b := by
  induction h with
  | refl =>
    -- By induction on `h`, `b` becomes `a`.
    -- The goal `P b` becomes `P a`, which we already have!
    exact ha


/- 4. Concrete Usage Examples -/

-- Let's prove a mathematical statement using our custom equality!
-- If x = y and z = y, then x = z.
example {A : Type} {x y z : A}
  (h1 : Eq x y) (h2 : Eq z y) : Eq x z := by
  -- First, we flip `z = y` to `y = z`
  have h2_flipped : Eq y z := Eq.symm h2

  -- Then we chain `x = y` and `y = z` together
  exact Eq.trans h1 h2_flipped


/- 5. Proving things are NOT equal -/

-- How do we prove `a ≠ b`?
-- In Lean, `Not P` means `P → False`.
-- So we assume they ARE equal, and derive a contradiction!

-- Let's define a simple property that distinguishes true and false
def IsTrue (b : Bool) : Prop :=
  match b with
  | true => True
  | false => False

-- Now we can prove that `true` does not equal `false` using our custom `Eq`
example : (Eq true false) → False := by
  intro h

  -- We know `IsTrue true` is trivially True
  have h_true : IsTrue true := trivial

  -- We use our substitution theorem!
  -- Since `true = false`, we can replace `true` with `false` in `IsTrue`
  have h_false : IsTrue false := Eq.subst IsTrue h h_true

  -- But `IsTrue false` evaluates definitionally to `False`!
  exact h_false


/-
This is equality in dependent type theory.
`Eq a b` is a type that depends on a and b.
Because `Eq a b` can only be built by `refl`,
applying induction to an equality proof automatically
instructs Lean's type checker to globally
search-and-replace `b` with `a`.
This single mechanism naturally gives rise to symmetry,
transitivity, function congruence, and rewriting!
-/


/-
In Homotopy Type Theory (HoTT), Martin-Löf's identity type
(the exact Eq type you just wrote) is reinterpreted topologically.

Even though standard Lean do not support HoTT,
we can actually the code slightly to reveal the geometry.
-/

/- The topological interpretation of equality in HoTT

In HoTT, we read `Eq a b` as "a path from point a to point b" in a space A.

1. Eq a b (Types): A topological space of paths between a and b.
2. refl: The constant path (standing still at point a).
3. symm: Walking a path backwards.
4. trans: Gluing two paths together end-to-end.
5. congrArg: If you continuously map a space A to B,
   a path in A becomes a path in B.
-/

/-
If we define equality by
`inductive Eq {A :Type} : A → A → Prop`
by the design of proof irrelevance,
Lean strictly assumes that any two proofs of the same Prop are
completely indistinguishable.

To see the HoTT behavior, all we have to do is to rewrite the code
and change Prop to Type. Put the identity type in
the universe of data (Type).
This forces Lean to treat paths as unique geometric objects
-/

namespace LectureHoTT

/- 1. The Path Type
  `Path` is defined as in `Quiver`.
-/

inductive Path {A : Type} : A → A → Type
  | refl (a : A) : Path a a

/- 2. Path Algebra (Pattern matching instead of tactics) -/

-- Path reversal (formerly symm)
-- if there is a path from `a` to `b`, then there is a path from `b` to `a`
-- We pattern match on `p`. If `p` is `refl a`, then `b` must be `a`,
def inv {A : Type} {a b : A} (p : Path a b) : Path b a :=
  match p with
  | Path.refl _ => Path.refl a

-- Path concatenation (formerly trans)
-- if there is a path from `a` to `b`, and a path from `b` to `c`
-- then there is a path from `a` to `c`.
def concat {A : Type} {a b c : A} (p : Path a b) (q : Path b c) : Path a c :=
  match q with
  | Path.refl _ => p


/- 3. Higher Geometry: Paths between Paths! -/

-- In math: p ⬝ refl = p
def concat_refl {A : Type} {a b : A} (p : Path a b) :
    Path (concat p (Path.refl b)) p :=
  -- Lean's definitional equality automatically
  -- reduces `concat p (refl b)` to `p`
  Path.refl p

-- In math: refl ⬝ p = p
-- We pattern match on `p`. If `p` is `refl a`, we need a path between
-- `concat (refl a) (refl a)` and `refl a`.
-- Both sides evaluate to `refl a`.
def refl_concat {A : Type} {a b : A} (p : Path a b) :
    Path (concat (Path.refl a) p) p :=
  match p with
  | Path.refl _ => Path.refl (Path.refl a)


/- 4. Function application to paths (Functoriality) -/

-- If you have a path from a to b, and a continuous function f,
-- you can push the path through the function to get a path
-- from f a to f b.
-- (This is `congrArg` from our earlier Eq example)
def ap {A B : Type} {a b : A} (f : A → B) (p : Path a b) : Path (f a) (f b) :=
  match p with
  | Path.refl _ => Path.refl (f a)


/- 5. The "Transport" Lemma -/

-- If you have a family of topological spaces `P : A → Type`
-- sitting above `A`, and you walk along a path from `a` to `b`
--  down in `A`, you can lift that path
-- to transport a point from the fiber over `a` to the fiber over `b`.
-- (This is `subst` or rewriting from our earlier Eq example)
def transport {A : Type} {a b : A} (P : A → Type) (p : Path a b) (x : P a) : P b :=
  match p with
  | Path.refl _ => x


/- Note:
When we match p against Path.refl _, the Lean typechecker
dynamically updates the expected return type. Initially,
it wants Path b a. But by matching refl _, Lean instantly
learns that b and a are definitionally identical. It
changes the expected return type to Path a a, allowing us
to simply return Path.refl a.

This is dependent type theory at its best!
-/


/- Note:
In Lean, the keyword theorem (and lemma) is strictly reserved
for things that live in Prop (logical statements).
Lean's compiler is designed to take anything marked as
a theorem and completely erase it from memory at runtime
to make your programs run faster (this is called "proof erasure").

But we have  changed Path from Prop to Type.
In HoTT, a path is not a "proof" that gets erased.
It is computational data (a geometric object).
Because it is data, we cannot use the theorem keyword.
You must use the def keyword, exactly as if we are writing
a regular programming function!
-/


/- EXAMPLE 1: Double Inverse (Involution)
   If you walk a path backwards, and then backwards again, you get
   the original path.
   Topologically: The path p⁻¹⁻¹ can be continuously deformed into p.
-/
def inv_inv {A : Type} {a b : A} (p : Path a b) :
    Path (inv (inv p)) p :=
  -- We pattern match on p.
  -- If p is just "standing still at a", then inv p is standing still,
  -- and inv (inv p) is standing still. Both sides become `Path.refl a`.
  match p with
  | Path.refl _ => Path.refl (Path.refl a)



/- EXAMPLE 2: Associativity of Path Gluing
   If you glue three paths together, it doesn't matter if you do (p ⬝ q) ⬝ r
   or p ⬝ (q ⬝ r).
   Topologically: This constructs the "associator" 2-path.
-/
def concat_assoc {A : Type} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path (concat (concat p q) r) (concat p (concat q r)) :=
  -- We pattern match on `r`.
  -- Why r? Because our `concat` function was defined by matching on its RIGHT argument.
  -- If `r` is `refl c`, then `concat q r` evaluates perfectly to `q`,
  -- and `concat (concat p q) r` evaluates to `concat p q`.
  -- Both sides become exactly `concat p q`!
  match r with
  | Path.refl _ => Path.refl (concat p q)


/- EXAMPLE 3: Functoriality of paths (Distributivity)
   If you apply a continuous function `f` to two glued paths,
   it is the same as applying `f` to the first path, and gluing it
   to `f` applied to the second path.
   In math: f(p ⬝ q) = f(p) ⬝ f(q)
-/
def ap_concat {A B : Type} {a b c : A} (f : A → B)
    (p : Path a b) (q : Path b c) :
    Path (ap f (concat p q)) (concat (ap f p) (ap f q)) :=
  -- Again, we match on `q` because `concat` computes on the right.
  -- If `q` is `refl b`, then `concat p q` reduces to `p`.
  -- The LHS becomes `ap f p`.
  -- The RHS `ap f q` becomes `refl (f b)`, so `concat (ap f p) (refl (f b))`
  -- also reduces to `ap f p`!
  match q with
  | Path.refl _ => Path.refl (ap f p)


/- EXAMPLE 4: Reversing a concatenated path
   If you walk along p and then q, and you want to reverse that whole journey,
   you must first walk backwards along q, and then backwards along p.
   In math: (p ⬝ q)⁻¹ = q⁻¹ ⬝ p⁻¹
-/
def inv_concat {A : Type} {a b c : A} (p : Path a b) (q : Path b c) :
    Path (inv (concat p q)) (concat (inv q) (inv p)) :=
  -- We match on `q`. If `q` is `refl b`, then `concat p q` becomes `p`.
  -- The LHS becomes `inv p`.
  -- On the RHS, `inv q` becomes `refl b`.
  -- The RHS becomes `concat (refl b) (inv p)`.
  -- Wait! Lean doesn't automatically know that `concat (refl b) (inv p)` is `inv p`.
  -- (Remember our `refl_concat` theorem? It requires a proof!)
  -- So we must ALSO pattern match on `p` to reduce the left side of the `concat`.
  match p, q with
  | Path.refl _, Path.refl _ =>
      -- Now p is `refl a` and q is `refl a`.
      -- Both sides evaluate perfectly to `refl a`.
      Path.refl (Path.refl a)



end LectureHoTT



end LectureEquality
