import MetaLang.Projection
import MetaLang.ObservationDiagram
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The algebra under multiple observation (v0.33, v0.34)

A continuation of `Projection.lean`: a single projection is replaced by a
family.

Contents:

* **The joint reconstruction theorem** (v0.33 §2). If the intersection of
  the family's kernels is trivial, the equational theory of the source is
  recovered from the observers' theories — **in both directions**.
* **The projection shadow** (v0.33 §3–§4). Without joint faithfulness an
  equation can be true for every observer and false in the source. The
  witness is the sign projection `S₃ → Bool`: the observed world is
  commutative, the source is not.
* **The blind kernel and active science** (v0.34 §1–§3). Adding an observer
  only narrows the blind relation; with a jointly faithful accessible class,
  every nontrivial blind remainder is split by some observer, and on a finite
  carrier the chain of strict refinements is finite.

The epistemic analogy "myth / superstition" (v0.33 §5, v0.34 §5) is **not**
formalized — the documents themselves forbid it; only the structural part
is.
-/

namespace MetaLang

universe u

/-- A family of observers compatible with the signature: every observer is a
surjective homomorphism. `ObsFamily` from `ObservationDiagram.lean` is left
untouched — the algebraic superstructure is kept separate. -/
structure AlgObsFamily (S : Type u) where
  /-- Observer indices. -/
  ι : Type u
  /-- The observed worlds. -/
  X : ι → Type u
  /-- The projections. -/
  O : ∀ i, S → X i
  /-- The signature of the source. -/
  sigS : Sig S
  /-- The signatures of the observed worlds. -/
  sigW : ∀ i, Sig (X i)
  /-- Every observer is a homomorphism. -/
  hom : ∀ i, sigS.Hom (sigW i) (O i)
  /-- Every observer is surjective. -/
  surj : ∀ i, Function.Surjective (O i)

namespace AlgObsFamily

variable {S : Type u} (F : AlgObsFamily S)

/-- The forgetful map into `ObsFamily`: the observation carrier is the same. -/
def toObsFamily : ObsFamily S := ⟨F.ι, F.X, F.O⟩

/-- The joint kernel of the family. -/
def Ker (x y : S) : Prop := ∀ i, F.O i x = F.O i y

/-- Joint faithfulness: the intersection of the kernels is the diagonal. -/
def Faithful : Prop := ∀ x y : S, F.Ker x y → x = y

variable {F}

/-- The equation holds in the source. -/
def HoldsS {V : Type u} (F : AlgObsFamily S) (t u : Term V) : Prop :=
  ∀ σ : V → S, Term.eval F.sigS σ t = Term.eval F.sigS σ u

/-- The equation holds in the world of observer `i`. -/
def HoldsW {V : Type u} (F : AlgObsFamily S) (i : F.ι) (t u : Term V) : Prop :=
  ∀ τ : V → F.X i, Term.eval (F.sigW i) τ t = Term.eval (F.sigW i) τ u

/-- **Descent of laws (v0.33 §1, gate `S5`).** Every equation of the source
holds for every observer. -/
theorem holdsW_of_holdsS {V : Type u} {t u : Term V} (i : F.ι)
    (h : F.HoldsS t u) : F.HoldsW i t u :=
  law_descends (F.hom i) (F.surj i) h

/-- **The joint reconstruction theorem (v0.33 §2).** A jointly faithful
family of observers recovers the equational theory of the source exactly: no
equation is lost and none is added. -/
theorem joint_reconstruction (hf : F.Faithful) {V : Type u} (t u : Term V) :
    (∀ i, F.HoldsW i t u) ↔ F.HoldsS t u := by
  constructor
  · intro h σ
    refine hf _ _ fun i => ?_
    have ht := Term.eval_hom (F.hom i) σ t
    have hu := Term.eval_hom (F.hom i) σ u
    rw [ht, hu]
    exact h i (F.O i ∘ σ)
  · intro h i
    exact holdsW_of_holdsS i h

/-! ## The epistemic hierarchy (v0.33 §7) -/

/-- A law is fundamental: it holds in the source. -/
def Fundamental {V : Type u} (F : AlgObsFamily S) (t u : Term V) : Prop :=
  F.HoldsS t u

/-- A law is exact in the declared observation domain. -/
def Scoped {V : Type u} (F : AlgObsFamily S) (t u : Term V) : Prop :=
  ∀ i, F.HoldsW i t u

/-- A law is a coherent shadow: exact for every observer and false in the
source. -/
def Shadow {V : Type u} (F : AlgObsFamily S) (t u : Term V) : Prop :=
  F.Scoped t u ∧ ¬ F.Fundamental t u

/-- **A shadow is possible only for an incomplete family (gate `S11` of
v0.33).** This is exactly the contrapositive of the joint reconstruction
theorem: a scientific domain that rejects a source law, or accepts a foreign
one, must fail to be jointly faithful. -/
theorem shadow_implies_not_faithful {V : Type u} {t u : Term V}
    (h : F.Shadow t u) : ¬ F.Faithful := by
  intro hf
  exact h.2 ((joint_reconstruction hf t u).mp h.1)

/-- The law is exact on the subfamily `I`. -/
def ScopedOn {V : Type u} (F : AlgObsFamily S) (I : Set F.ι) (t u : Term V) : Prop :=
  ∀ i ∈ I, F.HoldsW i t u

/-- **The set of universal laws only shrinks (v0.34 §4).** Adding an observer
can cancel a law but never create one. -/
theorem scopedOn_antitone {V : Type u} {t u : Term V} {I J : Set F.ι}
    (h : I ⊆ J) (hJ : F.ScopedOn J t u) : F.ScopedOn I t u :=
  fun i hi => hJ i (h hi)

/-! ## The blind kernel and active science (v0.34 §1–§3) -/

/-- The blind relation of a subfamily `I`: what none of the current
observers can yet tell apart. -/
def Blind (F : AlgObsFamily S) (I : Set F.ι) (x y : S) : Prop :=
  ∀ i ∈ I, F.O i x = F.O i y

/-- Unresolved pairs — the finite measure of the blind remainder. -/
def unresolved (F : AlgObsFamily S) (I : Set F.ι) : Set (S × S) :=
  {p | p.1 ≠ p.2 ∧ F.Blind I p.1 p.2}

/-- **The blind relation only narrows.** Adding an observer cannot restore a
lost indistinguishability. -/
theorem blind_antitone {I J : Set F.ι} (h : I ⊆ J) {x y : S}
    (hb : F.Blind J x y) : F.Blind I x y :=
  fun i hi => hb i (h hi)

theorem unresolved_antitone {I J : Set F.ι} (h : I ⊆ J) :
    F.unresolved J ⊆ F.unresolved I :=
  fun _ hp => ⟨hp.1, blind_antitone h hp.2⟩

/-- For a jointly faithful complete class, the blind relation over all
observers is the diagonal. -/
theorem unresolved_univ_empty (hf : F.Faithful) :
    F.unresolved (Set.univ : Set F.ι) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro p ⟨hne, hb⟩
  exact hne (hf p.1 p.2 fun i => hb i (Set.mem_univ i))

/-- **The refinement theorem (v0.34 §3).** If the blind remainder is
nontrivial and the full accessible class is jointly faithful, then some
observer splits that remainder: there is no dead end. -/
theorem exists_refining_observer (hf : F.Faithful) {I : Set F.ι}
    (h : (F.unresolved I).Nonempty) :
    ∃ (j : F.ι) (x y : S), x ≠ y ∧ F.Blind I x y ∧ F.O j x ≠ F.O j y := by
  obtain ⟨p, hne, hb⟩ := h
  by_cases hker : F.Ker p.1 p.2
  · exact absurd (hf p.1 p.2 hker) hne
  · simp only [Ker, not_forall] at hker
    obtain ⟨j, hj⟩ := hker
    exact ⟨j, p.1, p.2, hne, hb, hj⟩

/-- Strict refinement: the added observer removes at least one pair. -/
theorem unresolved_ssubset {I : Set F.ι} {j : F.ι} {x y : S}
    (hne : x ≠ y) (hb : F.Blind I x y) (hsplit : F.O j x ≠ F.O j y) :
    F.unresolved (insert j I) ⊂ F.unresolved I := by
  refine ⟨unresolved_antitone (Set.subset_insert j I), ?_⟩
  intro hsub
  have hmem : (x, y) ∈ F.unresolved I := ⟨hne, hb⟩
  have := hsub hmem
  exact hsplit (this.2 j (Set.mem_insert j I))

/-- **Zero gain from repetition (v0.34 §2).** An observer that splits nothing
beyond the current blind relation does not change the remainder — however
many times it is repeated. -/
theorem zero_gain_of_equivalent {I : Set F.ι} {j : F.ι}
    (h : ∀ x y : S, F.Blind I x y → F.O j x = F.O j y) :
    F.unresolved (insert j I) = F.unresolved I := by
  apply Set.eq_of_subset_of_subset (unresolved_antitone (Set.subset_insert j I))
  rintro p ⟨hne, hb⟩
  refine ⟨hne, ?_⟩
  intro i hi
  rcases Set.mem_insert_iff.mp hi with rfl | hi'
  · exact h p.1 p.2 hb
  · exact hb i hi'

/-- **Finite convergence of the active observer (v0.34 §3).** On a finite
carrier there is no infinite chain of strict refinements; hence any policy
whose every step yields positive gain reaches the diagonal in finitely many
steps. -/
theorem no_infinite_strict_refinement [Fintype S] [DecidableEq S]
    (seq : ℕ → Set F.ι)
    (hstrict : ∀ n, F.unresolved (seq (n + 1)) ⊂ F.unresolved (seq n)) : False := by
  have hfin : ∀ I : Set F.ι, (F.unresolved I).Finite := fun _ => Set.toFinite _
  have hlt : ∀ n, (F.unresolved (seq (n + 1))).ncard < (F.unresolved (seq n)).ncard :=
    fun n => Set.ncard_lt_ncard (hstrict n) (hfin _)
  have hbound : ∀ n, (F.unresolved (seq n)).ncard + n ≤ (F.unresolved (seq 0)).ncard := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have := hlt n
        omega
  have := hbound ((F.unresolved (seq 0)).ncard + 1)
  omega

end AlgObsFamily

/-! ## The shadow witness: the sign projection `S₃ → Bool` (v0.33 §3) -/

namespace ShadowWitness

open DihedralGroup

/-- The source is `S₃`, realized as `DihedralGroup 3`. -/
abbrev Src : Type := DihedralGroup 3

/-- The sign projection: a rotation is an even permutation, a reflection an
odd one. This is the quotient by `A₃` — exactly the observer class of
v0.33 §3. -/
def sgn : Src → Bool
  | .r _ => false
  | .sr _ => true

/-- The source signature: group multiplication, division, and the identity
reflection. -/
def sigSrc : Sig Src := ⟨fun x y => x * y, fun x y => x * y⁻¹, id⟩

/-- The signature of the observed world: `Bool` with exclusive or. -/
def sigBool : Sig Bool := ⟨xor, xor, id⟩

theorem sgn_mul (x y : Src) : sgn (x * y) = xor (sgn x) (sgn y) := by
  cases x <;> cases y <;> rfl

theorem sgn_inv (x : Src) : sgn x⁻¹ = sgn x := by
  cases x <;> rfl

theorem sgn_hom : sigSrc.Hom sigBool sgn := by
  refine ⟨fun x y => sgn_mul x y, fun x y => ?_, fun x => rfl⟩
  rw [sigSrc, sigBool]
  simp only
  rw [sgn_mul, sgn_inv]

theorem sgn_surjective : Function.Surjective sgn := by
  intro b
  cases b with
  | false => exact ⟨.r 0, rfl⟩
  | true => exact ⟨.sr 0, rfl⟩

/-- The observed world is commutative. -/
theorem bool_comm (a b : Bool) : sigBool.oplus a b = sigBool.oplus b a := by
  cases a <;> cases b <;> rfl

/-- The source is not. -/
theorem src_not_comm : ∃ x y : Src, x * y ≠ y * x := by
  refine ⟨.r 1, .sr 0, ?_⟩
  decide

/-! ### A one-observer family: the shadow -/

/-- The family consisting of the sign projection alone. -/
abbrev shadowFamily : AlgObsFamily Src where
  ι := Unit
  X := fun _ => Bool
  O := fun _ => sgn
  sigS := sigSrc
  sigW := fun _ => sigBool
  hom := fun _ => sgn_hom
  surj := fun _ => sgn_surjective

/-- The commutativity equation as a pair of terms. -/
def commT : Term (Fin 2) := .oplus (.var 0) (.var 1)

/-- The right-hand side of the same equation. -/
def commU : Term (Fin 2) := .oplus (.var 1) (.var 0)

/-- **Commutativity is exact for every observer of the family.** -/
theorem shadow_scoped : shadowFamily.Scoped commT commU := by
  intro _ τ
  exact bool_comm (τ 0) (τ 1)

/-- **And false in the source (gates `S8` of v0.33, `S2` of v0.34).** -/
theorem shadow_not_fundamental : ¬ shadowFamily.Fundamental commT commU := by
  intro h
  obtain ⟨x, y, hne⟩ := src_not_comm
  have hxy := h (fun k => if k = 0 then x else y)
  exact hne (by simpa [commT, commU, Term.eval, sigSrc] using hxy)

/-- **A coherent shadow exists.** A law true for all observers and false in
the source is not a measurement error but a property of the common
quotient. -/
theorem commutativity_is_a_shadow : shadowFamily.Shadow commT commU :=
  ⟨shadow_scoped, shadow_not_fundamental⟩

/-- By the theorem of §2, the family is not jointly faithful. -/
theorem shadowFamily_not_faithful : ¬ shadowFamily.Faithful :=
  AlgObsFamily.shadow_implies_not_faithful commutativity_is_a_shadow

/-! ### The active step: adding a separating observer (v0.34 §4) -/

/-- The observed worlds of the extended family. -/
def actX : Bool → Type
  | false => Bool
  | true => Src

/-- Its observers: the sign projection and the identity. -/
def actO : ∀ b, Src → actX b
  | false => sgn
  | true => id

/-- Its signatures. -/
def actSig : ∀ b, Sig (actX b)
  | false => sigBool
  | true => sigSrc

/-- The family extended by the identity observer: it separates everything
the sign projection glues. -/
abbrev activeFamily : AlgObsFamily Src where
  ι := Bool
  X := actX
  O := actO
  sigS := sigSrc
  sigW := actSig
  hom := by
    intro b
    cases b with
    | false => exact sgn_hom
    | true => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  surj := by
    intro b
    cases b with
    | false => exact sgn_surjective
    | true => exact Function.surjective_id

/-- **The extended family is jointly faithful.** -/
theorem activeFamily_faithful : activeFamily.Faithful := by
  intro x y h
  exact h true

/-- **The active step falsifies the shadow (gates `S7` of v0.33, `S21` of
v0.34).** This is "a jointly faithful family rejects false commutativity":
the two-way theorem of §2 supplies the criterion and it is applied here.
After a separating observer is added, commutativity ceases to be universally
true in the family. -/
theorem active_refutes_shadow : ¬ activeFamily.Scoped commT commU := by
  intro h
  have hS := (AlgObsFamily.joint_reconstruction activeFamily_faithful commT commU).mp h
  obtain ⟨x, y, hne⟩ := src_not_comm
  have hxy := hS (fun k => if k = 0 then x else y)
  exact hne (by simpa [commT, commU, Term.eval, sigSrc] using hxy)

/-! ### The shadow is not alone: there are several false equations -/

/-- The cube: `(x ⊕ x) ⊕ x`. -/
def cubeT : Term (Fin 2) := .oplus (.oplus (.var 0) (.var 0)) (.var 0)

/-- The right-hand side: `x` itself. -/
def cubeU : Term (Fin 2) := .var 0

/-- The square on the left. -/
def sqT : Term (Fin 2) := .oplus (.var 0) (.var 0)

/-- The square on the right. -/
def sqU : Term (Fin 2) := .oplus (.var 1) (.var 1)

theorem cube_scoped : shadowFamily.Scoped cubeT cubeU := by
  intro _ τ
  cases h : τ 0 <;> simp [cubeT, cubeU, Term.eval, sigBool, h]

theorem cube_not_fundamental : ¬ shadowFamily.Fundamental cubeT cubeU := by
  intro h
  have hxy := h (fun _ => (DihedralGroup.r 1 : Src))
  simp only [cubeT, cubeU, Term.eval, sigSrc] at hxy
  revert hxy
  decide

/-- **The exponent-2 law is exact on the observed class (gate `S10` of v0.33).** -/
theorem sq_scoped : shadowFamily.Scoped sqT sqU := by
  intro _ τ
  cases h0 : τ 0 <;> cases h1 : τ 1 <;> simp [sqT, sqU, Term.eval, sigBool, h0, h1]

theorem sq_not_fundamental : ¬ shadowFamily.Fundamental sqT sqU := by
  intro h
  have hxy := h (fun k => if k = 0 then (DihedralGroup.r 1 : Src) else DihedralGroup.sr 0)
  simp only [sqT, sqU, Term.eval, sigSrc] at hxy
  revert hxy
  decide

/-- **A non-faithful family carries several false source equations (gate
`S9` of v0.33).** Commutativity, the cube and the exponent-2 law are three
distinct equations, exact for every observer and false in the source. -/
theorem multiple_false_equations :
    shadowFamily.Shadow commT commU ∧
    shadowFamily.Shadow cubeT cubeU ∧
    shadowFamily.Shadow sqT sqU :=
  ⟨commutativity_is_a_shadow, ⟨cube_scoped, cube_not_fundamental⟩,
    ⟨sq_scoped, sq_not_fundamental⟩⟩

/-- **Exhausting the law grammar does not certify completeness (v0.34 §6).**
The family `shadowFamily` passes the equation `commT = commU` on every
observer — and that gives no ground whatsoever for concluding that the law
holds in the source. -/
theorem exhaustion_is_not_completeness :
    shadowFamily.Scoped commT commU ∧ ¬ shadowFamily.Fundamental commT commU ∧
      ¬ shadowFamily.Faithful :=
  ⟨shadow_scoped, shadow_not_fundamental, shadowFamily_not_faithful⟩

/-! ### Repeating an observer (v0.34 `S1`, `S13`, `S14`) -/

/-- A family consisting of arbitrarily many **copies** of one observer. -/
abbrev repeatedFamily (κ : Type) [Nonempty κ] : AlgObsFamily Src where
  ι := κ
  X := fun _ => Bool
  O := fun _ => sgn
  sigS := sigSrc
  sigW := fun _ => sigBool
  hom := fun _ => sgn_hom
  surj := fun _ => sgn_surjective

/-- **The starting family has a nontrivial blind relation (gate `S1`
v0.34).** -/
theorem repeated_blind_nontrivial (κ : Type) [Nonempty κ] :
    ∃ x y : Src, x ≠ y ∧ (repeatedFamily κ).Blind Set.univ x y := by
  refine ⟨DihedralGroup.r 0, DihedralGroup.r 1, by decide, fun _ _ => rfl⟩

/-- **Repetition never makes a family jointly faithful (gate `S14` of
v0.34).** However many copies of one observer are added, the hidden pair
stays hidden. -/
theorem repeated_not_faithful (κ : Type) [Nonempty κ] :
    ¬ (repeatedFamily κ).Faithful := by
  intro h
  have hxy : (DihedralGroup.r 0 : Src) = DihedralGroup.r 1 :=
    h (DihedralGroup.r 0) (DihedralGroup.r 1) (fun _ => rfl)
  revert hxy
  decide

/-- **Repetition does not remove false universal laws (gate `S13` of
v0.34).** The shadow survives any number of copies. -/
theorem repeated_keeps_shadow (κ : Type) [Nonempty κ] :
    (repeatedFamily κ).Shadow commT commU := by
  refine ⟨fun _ τ => bool_comm (τ 0) (τ 1), ?_⟩
  intro h
  obtain ⟨x, y, hne⟩ := src_not_comm
  have hxy := h (fun k => if k = 0 then x else y)
  exact hne (by simpa [commT, commU, Term.eval, sigSrc] using hxy)

/-! ### Zero false positives does not certify faithfulness (v0.34 `S26`, `S27`) -/

/-- A trivially true equation. -/
def trivT : Term (Fin 2) := .oplus (.var 0) (.var 1)

/-- **Absence of false positives on a finite grammar does not certify joint
faithfulness (gates `S26`, `S27` of v0.34).** On a grammar consisting of one
identically true equation, a non-faithful family makes no error at all — and
still fails to be faithful. -/
theorem zero_false_positives_does_not_certify :
    shadowFamily.Scoped trivT trivT ∧
    shadowFamily.Fundamental trivT trivT ∧
    ¬ shadowFamily.Faithful :=
  ⟨fun _ _ => rfl, fun _ => rfl, shadowFamily_not_faithful⟩

end ShadowWitness

end MetaLang
