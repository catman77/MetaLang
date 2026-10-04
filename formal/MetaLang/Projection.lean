import MetaLang.AlgebraicDescent

/-!
# Projection descent for the algebra (v0.32 §3–§5)

The third checkpoint of the meaning algebra: what happens to an operation
when the semantic source is projected onto an observer's world.

The central claim of v0.32 §3 is a criterion, not a sufficient condition:

  a quotient operation `μ̄` exists **if and only if** the kernel of the
  projection is a congruence for `μ`.

Hence v0.32 §4: if all the basic operations descend, then every term
descends, and therefore every equation. A law of the observed world is not a
description applied from outside but an invariant that survived the
projection.

The failure mode (v0.32 §5) matters just as much: if a hidden coordinate
affects the result, the kernel is not a congruence, and the source's
equations need **not** define an observable law.
-/

namespace MetaLang

universe u

namespace Projection

variable {S W : Type u}

/-! ## Congruence of the kernel -/

/-- The kernel of a projection is a congruence for a binary operation. -/
def Congruence₂ (π : S → W) (μ : S → S → S) : Prop :=
  ∀ x x' y y' : S, π x = π x' → π y = π y' → π (μ x y) = π (μ x' y')

/-- The kernel of a projection is a congruence for a unary operation. -/
def Congruence₁ (π : S → W) (r : S → S) : Prop :=
  ∀ x x' : S, π x = π x' → π (r x) = π (r x')

/-- The commuting square: `μ̄` realizes `μ` on the image. -/
def Descends (π : S → W) (μ : S → S → S) (μbar : W → W → W) : Prop :=
  ∀ x y : S, π (μ x y) = μbar (π x) (π y)

/-- **Necessity (v0.32 §3).** Congruence follows immediately from the
existence of a quotient operation. -/
theorem congruence_of_descends {π : S → W} {μ : S → S → S} {μbar : W → W → W}
    (h : Descends π μ μbar) : Congruence₂ π μ := by
  intro x x' y y' hx hy
  rw [h x y, h x' y', hx, hy]

open scoped Classical

/-- The quotient operation built on representatives. -/
noncomputable def push (π : S → W) (hsurj : Function.Surjective π)
    (μ : S → S → S) : W → W → W :=
  fun a b => π (μ (Classical.choose (hsurj a)) (Classical.choose (hsurj b)))

theorem push_descends {π : S → W} (hsurj : Function.Surjective π)
    {μ : S → S → S} (hcong : Congruence₂ π μ) :
    Descends π μ (push π hsurj μ) := by
  intro x y
  exact hcong x _ y _
    (Classical.choose_spec (hsurj (π x))).symm
    (Classical.choose_spec (hsurj (π y))).symm

/-- **Sufficiency and uniqueness (v0.32 §3).** For a surjective projection,
congruence of the kernel is equivalent to the existence of a unique quotient
operation. -/
theorem exists_unique_quotient_op {π : S → W} (hsurj : Function.Surjective π)
    {μ : S → S → S} (hcong : Congruence₂ π μ) :
    ∃! μbar : W → W → W, Descends π μ μbar := by
  refine ⟨push π hsurj μ, push_descends hsurj hcong, ?_⟩
  intro ν hν
  funext a b
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  rw [← hν x y, push_descends hsurj hcong x y]

/-- **The criterion (v0.32 §3).** A quotient operation exists exactly when
the kernel of the projection is a congruence. -/
theorem descends_iff_congruence {π : S → W} (hsurj : Function.Surjective π)
    (μ : S → S → S) :
    (∃ μbar : W → W → W, Descends π μ μbar) ↔ Congruence₂ π μ := by
  constructor
  · rintro ⟨μbar, h⟩
    exact congruence_of_descends h
  · intro hcong
    exact ⟨push π hsurj μ, push_descends hsurj hcong⟩

/-! ## Bridge to M8: congruence and requirement (2) -/

/-- **The condition of v0.32 §3 and requirement (2) of v0.22 §8 are one and
the same.** For the canonical projection onto the semantic quotient,
congruence of the kernel literally coincides with descent compatibility from
`MeaningAlgebra.lean`. -/
theorem congruence_iff_descentCompat (M : Machine.{u}) (op : M.St → M.St → M.St) :
    Congruence₂ (Quotient.mk (Machine.indistSetoid M)) op ↔ M.DescentCompat₂ op := by
  constructor
  · intro h x x' y y' hx hy
    exact Quotient.exact (h x x' y y' (Quotient.sound hx) (Quotient.sound hy))
  · intro h x x' y y' hx hy
    exact Quotient.sound (h x x' y y' (Quotient.exact hx) (Quotient.exact hy))

/-! ## Descent of equations (v0.32 §4, v0.33 §1) -/

/-- **The projection form of equation transport.** A surjective homomorphism
of the signature transports every equation of the signature; this is
`law_descends` from `AlgebraicDescent.lean` in the vocabulary of
projections. -/
theorem equation_descends {A : Sig S} {B : Sig W} {π : S → W}
    (h : A.Hom B π) (hsurj : Function.Surjective π) {V : Type u} {t u : Term V}
    (hS : ∀ σ : V → S, Term.eval A σ t = Term.eval A σ u) :
    ∀ τ : V → W, Term.eval B τ t = Term.eval B τ u :=
  law_descends h hsurj hS

/-- **Associativity descends (gate `S19` of v0.32, `S5` of v0.33).** -/
theorem assoc_descends {A : Sig S} {B : Sig W} {π : S → W}
    (h : A.Hom B π) (hsurj : Function.Surjective π)
    (hA : ∀ x y z : S, A.oplus (A.oplus x y) z = A.oplus x (A.oplus y z)) :
    ∀ a b c : W, B.oplus (B.oplus a b) c = B.oplus a (B.oplus b c) := by
  intro a b c
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  obtain ⟨z, rfl⟩ := hsurj c
  rw [← h.1, ← h.1, ← h.1, ← h.1, hA]

/-- Commutativity descends by the same argument. -/
theorem comm_descends {A : Sig S} {B : Sig W} {π : S → W}
    (h : A.Hom B π) (hsurj : Function.Surjective π)
    (hA : ∀ x y : S, A.oplus x y = A.oplus y x) :
    ∀ a b : W, B.oplus a b = B.oplus b a := by
  intro a b
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  rw [← h.1, ← h.1, hA]

end Projection

/-! ## The nuisance-coordinate witness (v0.32 §5) -/

namespace Nuisance

/-- The source: one observable coordinate and one hidden. -/
abbrev Src : Type := Bool × Bool

/-- The projection forgets the hidden coordinate. -/
def proj : Src → Bool := Prod.fst

theorem proj_surjective : Function.Surjective proj := fun b => ⟨(b, false), rfl⟩

/-- An operation whose result depends on the **hidden** coordinate of the
second operand. -/
def badOp : Src → Src → Src := fun x y => (xor x.1 y.2, x.2)

/-- An operation that uses only the observable coordinates. -/
def goodOp : Src → Src → Src := fun x y => (x.1 && y.1, x.2)

/-- **Nuisance breaks congruence (gates `S20`, `S21` of v0.32).** No
commuting square exists: two operands with the same projection give
different observable results. -/
theorem nuisance_breaks_congruence : ¬ Projection.Congruence₂ proj badOp := by
  intro h
  have := h (true, false) (true, false) (false, true) (false, false) rfl rfl
  revert this
  decide

/-- Consequently there is no quotient operation at all. -/
theorem nuisance_has_no_quotient_op :
    ¬ ∃ μbar : Bool → Bool → Bool, Projection.Descends proj badOp μbar := by
  rw [Projection.descends_iff_congruence proj_surjective]
  exact nuisance_breaks_congruence

/-- **A projection preserves the algebra while removing nuisance (gate `S25`
of v0.32).** The same projection, with an operation independent of the hidden
coordinate, descends — and does so uniquely. -/
theorem good_descends : Projection.Congruence₂ proj goodOp := by
  intro x x' y y' hx hy
  simp only [proj, goodOp] at *
  rw [hx, hy]

theorem good_quotient_is_and :
    Projection.Descends proj goodOp (fun a b => a && b) := by
  intro x y
  rfl

end Nuisance

end MetaLang
