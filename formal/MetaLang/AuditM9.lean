import MetaLang.AuditM8
import MetaLang.OperationalAlgebra

/-!
# Audit of the algebra under observation (M9)

The same discipline as in `Countermodels.lean`, `Audit.lean`, `AuditM7.lean`
and `AuditM8.lean`. Phases R1–R7: projection descent, joint reconstruction,
the projection shadow, the blind kernel, and the equational theory of the
operational object.

The strong claims the corpus **rejects** — above all "a law true for all
observers is true in the source" — are encoded as refuted, with the
homomorphism `S₃ → Bool` as witness.
-/

namespace MetaLang

namespace AuditM9

open Projection AlgObsFamily ShadowWitness

/-! ### R1: projection descent -/

/-- Failure: the kernel is a congruence, yet there is no quotient operation. -/
def QuotientOpFailure : Prop :=
  ∃ (S W : Type) (π : S → W) (_ : Function.Surjective π) (μ : S → S → S),
    Congruence₂ π μ ∧ ¬ ∃ μbar, Descends π μ μbar

theorem no_quotientOpFailure : ¬ QuotientOpFailure := by
  rintro ⟨S, W, π, hsurj, μ, hcong, h⟩
  exact h ((descends_iff_congruence hsurj μ).mpr hcong)

/-- Failure: a quotient operation exists, yet the kernel is not a congruence. -/
def CongruenceNecessityFailure : Prop :=
  ∃ (S W : Type) (π : S → W) (μ : S → S → S) (μbar : W → W → W),
    Descends π μ μbar ∧ ¬ Congruence₂ π μ

theorem no_congruenceNecessityFailure : ¬ CongruenceNecessityFailure := by
  rintro ⟨S, W, π, μ, μbar, hd, h⟩
  exact h (congruence_of_descends hd)

/-- Failure of the **strong** claim: every total operation could descend
through every projection. Refuted by the nuisance coordinate. -/
def AllOpsDescendFailure : Prop :=
  ∀ (μ : Nuisance.Src → Nuisance.Src → Nuisance.Src), Congruence₂ Nuisance.proj μ

theorem no_allOpsDescendFailure : ¬ AllOpsDescendFailure := by
  intro h
  exact Nuisance.nuisance_breaks_congruence (h Nuisance.badOp)

/-- Failure: associativity of the source does not reach the quotient. -/
def AssocDescentFailure : Prop :=
  ∃ (S W : Type) (A : Sig S) (B : Sig W) (π : S → W),
    A.Hom B π ∧ Function.Surjective π ∧
    (∀ x y z, A.oplus (A.oplus x y) z = A.oplus x (A.oplus y z)) ∧
    ∃ a b c, B.oplus (B.oplus a b) c ≠ B.oplus a (B.oplus b c)

theorem no_assocDescentFailure : ¬ AssocDescentFailure := by
  rintro ⟨S, W, A, B, π, hhom, hsurj, hA, a, b, c, hne⟩
  exact hne (assoc_descends hhom hsurj hA a b c)

/-- Failure: congruence of the canonical projection diverges from
requirement (2) of `MeaningAlgebra.lean`. -/
def CongruenceBridgeFailure : Prop :=
  ∃ (M : Machine.{0}) (op : M.St → M.St → M.St),
    ¬ (Congruence₂ (Quotient.mk (Machine.indistSetoid M)) op ↔ M.DescentCompat₂ op)

theorem no_congruenceBridgeFailure : ¬ CongruenceBridgeFailure := by
  rintro ⟨M, op, h⟩
  exact h (congruence_iff_descentCompat M op)

/-! ### R2–R3: descent of laws and joint reconstruction -/

/-- Failure: a law of the source fails for an observer. -/
def LawToObserverFailure : Prop :=
  ∃ (S : Type) (F : AlgObsFamily S) (V : Type) (t u : Term V) (i : F.ι),
    F.HoldsS t u ∧ ¬ F.HoldsW i t u

theorem no_lawToObserverFailure : ¬ LawToObserverFailure := by
  rintro ⟨S, F, V, t, u, i, hS, h⟩
  exact h (holdsW_of_holdsS i hS)

/-- Failure: a jointly faithful family fails to recover the theory of the source. -/
def JointReconstructionFailure : Prop :=
  ∃ (S : Type) (F : AlgObsFamily S) (V : Type) (t u : Term V),
    F.Faithful ∧ (∀ i, F.HoldsW i t u) ∧ ¬ F.HoldsS t u

theorem no_jointReconstructionFailure : ¬ JointReconstructionFailure := by
  rintro ⟨S, F, V, t, u, hf, hW, h⟩
  exact h ((joint_reconstruction hf t u).mp hW)

/-! ### R4: the projection shadow -/

/-- Failure: a shadow for a jointly faithful family. -/
def FaithfulShadowFailure : Prop :=
  ∃ (S : Type) (F : AlgObsFamily S) (V : Type) (t u : Term V),
    F.Shadow t u ∧ F.Faithful

theorem no_faithfulShadowFailure : ¬ FaithfulShadowFailure := by
  rintro ⟨S, F, V, t, u, hsh, hf⟩
  exact shadow_implies_not_faithful hsh hf

/-- Failure of the **strong** claim: a law exact for every observer could be
a law of the source. Refuted by the sign projection `S₃ → Bool`. -/
def ObservedLawIsSourceLawFailure : Prop :=
  shadowFamily.Scoped commT commU → shadowFamily.Fundamental commT commU

theorem no_observedLawIsSourceLawFailure : ¬ ObservedLawIsSourceLawFailure := by
  intro h
  exact shadow_not_fundamental (h shadow_scoped)

/-- Failure of the **strong** claim: exhausting the grammar of laws could
certify completeness of the observer class. -/
def ExhaustionCertifiesFailure : Prop :=
  shadowFamily.Scoped commT commU → shadowFamily.Faithful

theorem no_exhaustionCertifiesFailure : ¬ ExhaustionCertifiesFailure := by
  intro h
  exact shadowFamily_not_faithful (h shadow_scoped)

/-- Failure of the **strong** claim: the shadow could survive the active
step — commutativity would stay exact even after a separating observer is
added. Refuted by joint faithfulness of the extended family (gates `S7` of
v0.33, `S21` of v0.34). -/
def ActiveStepFailure : Prop := activeFamily.Scoped commT commU

theorem no_activeStepFailure : ¬ ActiveStepFailure := active_refutes_shadow

/-! ### R5: the blind kernel -/

/-- Failure: adding an observer enlarges the blind remainder. -/
def BlindMonotoneFailure : Prop :=
  ∃ (S : Type) (F : AlgObsFamily S) (I : Set F.ι) (j : F.ι),
    ¬ F.unresolved (insert j I) ⊆ F.unresolved I

theorem no_blindMonotoneFailure : ¬ BlindMonotoneFailure := by
  rintro ⟨S, F, I, j, h⟩
  exact h (unresolved_antitone (Set.subset_insert j I))

/-- Failure: the blind remainder is nontrivial, the class is jointly
faithful, and yet no separating observer exists — a dead end. -/
def DeadlockFailure : Prop :=
  ∃ (S : Type) (F : AlgObsFamily S) (I : Set F.ι),
    F.Faithful ∧ (F.unresolved I).Nonempty ∧
    ¬ ∃ (j : F.ι) (x y : S), x ≠ y ∧ F.Blind I x y ∧ F.O j x ≠ F.O j y

theorem no_deadlockFailure : ¬ DeadlockFailure := by
  rintro ⟨S, F, I, hf, hne, h⟩
  exact h (exists_refining_observer hf hne)

/-- Failure: an observer that distinguishes nothing beyond the current ones
still changes the remainder. -/
def ZeroGainFailure : Prop :=
  ∃ (S : Type) (F : AlgObsFamily S) (I : Set F.ι) (j : F.ι),
    (∀ x y : S, F.Blind I x y → F.O j x = F.O j y) ∧
    F.unresolved (insert j I) ≠ F.unresolved I

theorem no_zeroGainFailure : ¬ ZeroGainFailure := by
  rintro ⟨S, F, I, j, hcond, h⟩
  exact h (zero_gain_of_equivalent hcond)

/-! ### R6: the equational theory of the operational object -/

/-- Failure: the canonical projection onto the operational object is not a homomorphism. -/
def OpAlgebraFailure : Prop :=
  ∃ (S : Type) (F : AlgObsFamily S), ¬ F.sigS.Hom F.opSig F.toOp

theorem no_opAlgebraFailure : ¬ OpAlgebraFailure := by
  rintro ⟨S, F, h⟩
  exact h F.toOp_hom

/-- Failure: associativity of the source is lost in the operational object. -/
def OpAssocFailure : Prop :=
  ∃ (S : Type) (F : AlgObsFamily S),
    (∀ x y z : S, F.sigS.oplus (F.sigS.oplus x y) z =
      F.sigS.oplus x (F.sigS.oplus y z)) ∧
    ∃ a b c : F.OpObject, F.opSig.oplus (F.opSig.oplus a b) c ≠
      F.opSig.oplus a (F.opSig.oplus b c)

theorem no_opAssocFailure : ¬ OpAssocFailure := by
  rintro ⟨S, F, hA, a, b, c, hne⟩
  exact hne (F.opSig_assoc hA a b c)

/-- Failure: the theory of the operational object diverges from the common
theory of the observers. -/
def OpTheoryFailure : Prop :=
  ∃ (S : Type) (F : AlgObsFamily S) (V : Type) (t u : Term V),
    ¬ (F.HoldsOp t u ↔ ∀ i, F.HoldsW i t u)

theorem no_opTheoryFailure : ¬ OpTheoryFailure := by
  rintro ⟨S, F, V, t, u, h⟩
  exact h (F.holdsOp_iff_forall_holdsW t u)

/-- Failure of the **strong** claim: the operational object could always
agree with the source on equations. Refuted by the shadow: commutativity
holds in `S_op` and fails in `S`. -/
def OpObjectIsSourceFailure : Prop :=
  shadowFamily.HoldsOp commT commU → shadowFamily.HoldsS commT commU

theorem no_opObjectIsSourceFailure : ¬ OpObjectIsSourceFailure := by
  intro h
  exact opObject_commutative_source_not.2 (h opObject_commutative_source_not.1)

/-! ### R7: catch-ups -/

/-- Failure: the refinement primitive is not idempotent. -/
def PrimitiveIdempotenceFailure : Prop :=
  ∃ z x : Bow, x ≤ z ∧
    (RefinementInterface.sys Bow).run [z, z] x ≠ (RefinementInterface.sys Bow).run [z] x

theorem no_primitiveIdempotenceFailure : ¬ PrimitiveIdempotenceFailure := by
  rintro ⟨z, x, hle, h⟩
  exact h (RefinementInterface.run_idempotent z x hle)

/-- Failure: reflection on the infinite Boolean carrier is not idempotent. -/
def InfiniteReflectionFailure : Prop :=
  ∃ (A : ℕ → Bool) (x : ℕ → Bool),
    Witnesses.InfiniteReflection.refl A (Witnesses.InfiniteReflection.refl A x) ≠
      Witnesses.InfiniteReflection.refl A x

theorem no_infiniteReflectionFailure : ¬ InfiniteReflectionFailure := by
  rintro ⟨A, x, h⟩
  exact h (Witnesses.InfiniteReflection.refl_idempotent x)

/-! ### The summary theorem -/

/-- **The audit of the algebra under observation passes.** Twenty failure
modes are closed: fifteen positive theorems and five refutations of strong
claims, each with a witness — either the homomorphism `S₃ → Bool` or the
nuisance coordinate. -/
theorem projection_audit_passes :
    (¬ QuotientOpFailure) ∧
    (¬ CongruenceNecessityFailure) ∧
    (¬ AllOpsDescendFailure) ∧
    (¬ AssocDescentFailure) ∧
    (¬ CongruenceBridgeFailure) ∧
    (¬ LawToObserverFailure) ∧
    (¬ JointReconstructionFailure) ∧
    (¬ FaithfulShadowFailure) ∧
    (¬ ObservedLawIsSourceLawFailure) ∧
    (¬ ExhaustionCertifiesFailure) ∧
    (¬ ActiveStepFailure) ∧
    (¬ BlindMonotoneFailure) ∧
    (¬ DeadlockFailure) ∧
    (¬ ZeroGainFailure) ∧
    (¬ OpAlgebraFailure) ∧
    (¬ OpAssocFailure) ∧
    (¬ OpTheoryFailure) ∧
    (¬ OpObjectIsSourceFailure) ∧
    (¬ PrimitiveIdempotenceFailure) ∧
    (¬ InfiniteReflectionFailure) :=
  ⟨no_quotientOpFailure,
   no_congruenceNecessityFailure,
   no_allOpsDescendFailure,
   no_assocDescentFailure,
   no_congruenceBridgeFailure,
   no_lawToObserverFailure,
   no_jointReconstructionFailure,
   no_faithfulShadowFailure,
   no_observedLawIsSourceLawFailure,
   no_exhaustionCertifiesFailure,
   no_activeStepFailure,
   no_blindMonotoneFailure,
   no_deadlockFailure,
   no_zeroGainFailure,
   no_opAlgebraFailure,
   no_opAssocFailure,
   no_opTheoryFailure,
   no_opObjectIsSourceFailure,
   no_primitiveIdempotenceFailure,
   no_infiniteReflectionFailure⟩

end AuditM9

end MetaLang
