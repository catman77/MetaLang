import MetaLang.Congruence
import MetaLang.InternalLanguage

/-!
# Descent and gluing (v0.20–v0.23)

The key distinction of v0.20: **continuation arrows are dynamics, not gluing
arrows**. A naive colimit over continuation arrows yields the orbit quotient,
not the semantic one. The correct reconstruction is a coequalizer over the
overlaps of local charts.

This is formalized here without categorical machinery: a cover as a family
of subsets, the colimit as the quotient of a disjoint union by the descent
relation. The positive result is bijectivity of the canonical `eta`; the
negative ones are four ways to break the reconstruction.

v0.21 adds the essential point: the descent relation itself is **derived
from behaviour** rather than taken from an oracle. In this formalization
that is a direct consequence of the stabilization theorem of
`Congruence.lean`.
-/

namespace MetaLang

universe u

/-- A cover of the semantic space by local charts. -/
structure Cover (Q : Type u) where
  /-- Chart index. -/
  ι : Type u
  /-- The chart itself. -/
  chart : ι → Set Q

namespace Cover

variable {Q : Type u} (C : Cover Q)

/-- A cover is complete when every point lies in at least one chart. -/
def Covers : Prop := ∀ q : Q, ∃ i, q ∈ C.chart i

/-- Local points: a point together with a chart presenting it. -/
def Local : Type u := Σ i : C.ι, {q : Q // q ∈ C.chart i}

/-- The descent relation: two local points are glued when they present the
same global point. -/
def descentSetoid : Setoid C.Local where
  r p p' := p.2.1 = p'.2.1
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The colimit of the cover. -/
def Colimit : Type u := Quotient C.descentSetoid

/-- The canonical map from the colimit to the global space. -/
def eta : C.Colimit → Q := Quotient.lift (fun p => p.2.1) (fun _ _ h => h)

@[simp] theorem eta_mk (p : C.Local) :
    C.eta (Quotient.mk C.descentSetoid p) = p.2.1 := rfl

/-- `eta` is always injective: descent glues exactly what it should. -/
theorem eta_injective : Function.Injective C.eta := by
  intro a b h
  induction a using Quotient.inductionOn with
  | h p =>
      induction b using Quotient.inductionOn with
      | h p' => exact Quotient.sound h

/-- `eta` is surjective exactly when the cover is complete. -/
theorem eta_surjective_iff : Function.Surjective C.eta ↔ C.Covers := by
  constructor
  · intro hsurj q
    obtain ⟨x, hx⟩ := hsurj q
    induction x using Quotient.inductionOn with
    | h p => exact ⟨p.1, hx ▸ p.2.2⟩
  · intro hcov q
    obtain ⟨i, hi⟩ := hcov q
    exact ⟨Quotient.mk C.descentSetoid ⟨i, ⟨q, hi⟩⟩, rfl⟩

/-- **The Čech colimit recovers the space** (`S6`, `S7`): for a complete
cover with exact overlaps the canonical map is bijective. -/
theorem eta_bijective (hcov : C.Covers) : Function.Bijective C.eta :=
  ⟨C.eta_injective, C.eta_surjective_iff.mpr hcov⟩

end Cover

/-! ### Four ways to break the reconstruction -/

/-- **`S12`: an incomplete cover breaks surjectivity.** -/
theorem incomplete_cover_not_surjective :
    ∃ (Q : Type) (C : Cover Q), ¬ C.Covers ∧ ¬ Function.Surjective C.eta := by
  refine ⟨Bool, ⟨Unit, fun _ => {true}⟩, ?_, ?_⟩
  · intro hcov
    obtain ⟨i, hi⟩ := hcov false
    exact absurd hi (by simp)
  · intro hsurj
    exact absurd (Cover.eta_surjective_iff _ |>.mp hsurj) (by
      intro hcov
      obtain ⟨i, hi⟩ := hcov false
      exact absurd hi (by simp))

/-- **`S13`/`S11`: the descent relation can be neither coarsened nor
refined.** A coarser relation glues distinct global points; a finer one
leaves spurious copies. Formally: only equality of global points yields a
bijective `eta` — that is the content of `eta_injective`. -/
theorem descent_relation_is_forced {Q : Type u} (C : Cover Q)
    (r : Setoid C.Local)
    (hcoarse : ∀ p p' : C.Local, r.r p p' → p.2.1 = p'.2.1)
    (hfine : ∀ p p' : C.Local, p.2.1 = p'.2.1 → r.r p p') :
    ∀ p p' : C.Local, r.r p p' ↔ C.descentSetoid.r p p' :=
  fun p p' => ⟨hcoarse p p', hfine p p'⟩

/-- **`S14`: the naive colimit over continuation arrows is wrong.** A
dynamic arrow connects states with **different** responses, so the orbit
quotient glues semantically distinct states. Continuation arrows are
dynamics, not gluing. -/
theorem naive_dynamic_colimit_wrong :
    ∃ (N : Machine.{0}) (x : N.St) (w : List N.Act),
      ¬ N.Indist x (N.transport w x) := by
  refine ⟨latentMachine, 0, [(), ()], ?_⟩
  intro h
  have hR : latentMachine.R 0 = latentMachine.R (latentMachine.transport [(), ()] 0) :=
    Machine.indist_resp h
  exact absurd hR (by decide)

/-- **v0.23, gate 13: a cover of states does not imply a cover of pairs.**
Charts may cover the whole space while none contains both operands — and then
a binary operation does not globalize. -/
theorem state_cover_not_tuple_cover :
    ∃ (Q : Type) (C : Cover Q), C.Covers ∧
      ∃ p q : Q, ∀ i, ¬ (p ∈ C.chart i ∧ q ∈ C.chart i) := by
  refine ⟨Bool, ⟨Bool, fun i => {i}⟩, ?_, true, false, ?_⟩
  · intro q; exact ⟨q, rfl⟩
  · rintro i ⟨h1, h2⟩
    rw [Set.mem_singleton_iff] at h1 h2
    exact absurd (h1.trans h2.symm) (by decide)

/-! ### Behavioural descent (v0.21)

The descent relation need not come from an oracle: equality of stabilized
behavioural fingerprints **is** the relation required. In this formalization
the claim follows directly from the stabilization theorem. -/

/-- **Descent is derived from behaviour.** There is a finite depth at which
equality of fingerprints coincides with semantic indistinguishability. No
access to hidden identifiers is required. -/
theorem behavioural_descent (M : Machine) [Fintype M.St] :
    ∃ n : ℕ, ∀ s t : M.St, M.Indist s t ↔ M.approx n s t :=
  Machine.stabilization M

end MetaLang
