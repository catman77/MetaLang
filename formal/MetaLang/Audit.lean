import MetaLang.Countermodels

/-!
# The final audit

Reduces the formalization to one machine-checked theorem and one status
table. The table distinguishes what is **proved** from what is **refuted**:
part of the corpus's content consists precisely of negative results, and in
the audit they must carry the same weight as the positive ones.
-/

namespace MetaLang

namespace Audit

/-- The status of a claim relative to the current formal core. -/
inductive ClaimStatus where
  /-- Proved. -/
  | proved
  /-- Proved under additional assumptions. -/
  | provedUnderExtraAxioms
  /-- Independent of the current core. -/
  | independent
  /-- Refuted by a countermodel. -/
  | refuted
  deriving DecidableEq, Repr

/-- The audit along the axes of the programme. -/
structure StrengthAudit where
  /-- Prefix closure, filters, noncommutativity. -/
  continuationCore : ClaimStatus
  /-- Stabilization of refinement on a finite source. -/
  stabilization : ClaimStatus
  /-- The limit is the greatest context congruence. -/
  maximality : ClaimStatus
  /-- Invariance under renaming of surface names. -/
  gaugeInvariance : ClaimStatus
  /-- Subdirect embedding of the operational object. -/
  subdirectEmbedding : ClaimStatus
  /-- The finite witness of operational equivalence `Q8`/`D8`. -/
  operationalEquivalence : ClaimStatus
  /-- Strong claim: science singles out a unique ontic source. -/
  uniqueOnticSource : ClaimStatus
  /-- Strong claim: the object profile suffices. -/
  profileSufficiency : ClaimStatus
  /-- Strong claim: structure determines value. -/
  structureImpliesUtility : ClaimStatus
  /-- Strong claim: correspondence implies a channel. -/
  correspondenceImpliesChannel : ClaimStatus
  /-- Strong claim: a partial fixed point is truth. -/
  partialFixedPointIsTruth : ClaimStatus

/-- The current classification. The last five axes are **refuted** — that is
exactly the content of the corpus's negative results. -/
def currentAudit : StrengthAudit where
  continuationCore := ClaimStatus.proved
  stabilization := ClaimStatus.proved
  maximality := ClaimStatus.proved
  gaugeInvariance := ClaimStatus.proved
  subdirectEmbedding := ClaimStatus.proved
  operationalEquivalence := ClaimStatus.proved
  uniqueOnticSource := ClaimStatus.refuted
  profileSufficiency := ClaimStatus.refuted
  structureImpliesUtility := ClaimStatus.refuted
  correspondenceImpliesChannel := ClaimStatus.refuted
  partialFixedPointIsTruth := ClaimStatus.refuted

/-- **The final audit theorem.** Every encoded failure mode is closed: the
positive claims do not fail, and the strong claims the corpus rejects are
genuinely refuted by countermodels. -/
theorem final_audit_passes :
    (¬ StabilizationFailure latentMachine) ∧
    (¬ WitnessFailure latentMachine) ∧
    (¬ CongruenceFailure latentMachine) ∧
    (¬ LegitimacyFailure latentMachine) ∧
    (¬ SubdirectFailure (Machine.wordFamily latentMachine)) ∧
    (¬ UnderdeterminationFailure) ∧
    (¬ ProfileSufficiencyFailure) ∧
    (¬ UtilityFailure) ∧
    (¬ ChannelFailure) ∧
    (¬ PartialTruthFailure) :=
  ⟨no_stabilizationFailure latentMachine,
   no_witnessFailure latentMachine,
   no_congruenceFailure latentMachine,
   no_legitimacyFailure latentMachine,
   no_subdirectFailure _,
   no_underdeterminationFailure,
   no_profileSufficiencyFailure,
   no_utilityFailure,
   no_channelFailure,
   no_partialTruthFailure⟩

/-- Gauge invariance is closed for **every** renaming, not just for a
chosen one. -/
theorem gauge_audit_passes {St' : Type} (e : latentMachine.St ≃ St') :
    ¬ GaugeFailure latentMachine e :=
  no_gaugeFailure latentMachine e

/-- The audit is recorded: six positive axes, five refuted. -/
theorem audit_shape :
    currentAudit.continuationCore = ClaimStatus.proved ∧
    currentAudit.stabilization = ClaimStatus.proved ∧
    currentAudit.maximality = ClaimStatus.proved ∧
    currentAudit.gaugeInvariance = ClaimStatus.proved ∧
    currentAudit.subdirectEmbedding = ClaimStatus.proved ∧
    currentAudit.operationalEquivalence = ClaimStatus.proved ∧
    currentAudit.uniqueOnticSource = ClaimStatus.refuted ∧
    currentAudit.profileSufficiency = ClaimStatus.refuted ∧
    currentAudit.structureImpliesUtility = ClaimStatus.refuted ∧
    currentAudit.correspondenceImpliesChannel = ClaimStatus.refuted ∧
    currentAudit.partialFixedPointIsTruth = ClaimStatus.refuted := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Audit

end MetaLang
