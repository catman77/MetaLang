import MetaLang.Audit
import MetaLang.ASCTopology
import MetaLang.CollapseBridge
import MetaLang.RefinementOrder
import MetaLang.Reflection
import MetaLang.ReflectorAlgebra
import MetaLang.ConstraintLogic
import MetaLang.TheorySpace
import MetaLang.Descent

/-!
# Audit of the ASC ladder (M7)

A continuation of `Countermodels.lean` and `Audit.lean` to phases N1–N8. The
same discipline: for every substantive claim, the way it could fail is
encoded, and that way is proved to be closed. Strong claims that the corpus
rejects are encoded as **refuted**.
-/

namespace MetaLang

namespace AuditM7

open Machine

/-! ### N1–N2: topology and scales -/

/-- Failure: the distinguishing depth is not an ultrametric. -/
def UltrametricFailure (M : Machine) : Prop :=
  ∃ x y z : M.St, ¬ (min (M.sep x y) (M.sep y z) ≤ M.sep x z)

theorem no_ultrametricFailure (M : Machine) : ¬ UltrametricFailure M := by
  rintro ⟨x, y, z, h⟩
  exact h (sep_ultrametric x y z)

/-- Failure: transport cuts the depth by more than one step. -/
def LipschitzFailure (M : Machine) : Prop :=
  ∃ (a : M.Act) (x y : M.St), ¬ (M.sep x y ≤ M.sep (M.T a x) (M.T a y) + 1)

theorem no_lipschitzFailure (M : Machine) : ¬ LipschitzFailure M := by
  rintro ⟨a, x, y, h⟩
  exact h (sep_le_sep_transport_succ a x y)

/-- Failure of a **strong** claim: a globally nonexpansive metric with
uniformly separated responses could be non-discrete. Refuted by the chain
witness. -/
def NonexpansiveNonDiscreteFailure : Prop :=
  ∀ (M : Machine.{0}) (P : GlobalMetric M) (δ : ℝ),
    P.UniformResponseSeparation δ → ∃ x y : M.St, ¬ M.Indist x y ∧ P.rho x y < δ

theorem no_nonexpansiveNonDiscreteFailure : ¬ NonexpansiveNonDiscreteFailure := by
  intro h
  obtain ⟨x, y, hne, hlt⟩ := h chainMachine (rhoInf chainMachine) 1 rhoInf_separation
  have := GlobalMetric.uniformly_discrete_of_nonexpansive _ rhoInf_separation hne
  exact absurd hlt (not_lt_of_ge this)

/-! ### N3–N5: order, synthesis, reflection -/

/-- Failure: the two bracketings of synthesis disagree. -/
def SynthesisAssocFailure : Prop :=
  ∃ (α : Type) (_ : PartialOrder α) (x y z u v w v' : α),
    IsSynthesis x y u ∧ IsSynthesis u z v ∧ IsSynthesis y z w ∧ IsSynthesis x w v' ∧ v ≠ v'

theorem no_synthesisAssocFailure : ¬ SynthesisAssocFailure := by
  rintro ⟨α, _, x, y, z, u, v, w, v', hu, hv, hw, hv', hne⟩
  exact hne (isSynthesis_assoc hu hv hw hv')

/-- Failure of a **strong** claim: the continuation order would determine a
unique binary operation. Refuted by the pair of projections. -/
def BinopDeterminedFailure : Prop :=
  ∀ (α : Type) (_ : PartialOrder α) (x y : α), x ≠ y →
    ∀ f g : α → α → α,
      (∀ a : α, Monotone (f a)) → (∀ b : α, Monotone (fun a => f a b)) →
      (∀ a : α, Monotone (g a)) → (∀ b : α, Monotone (fun a => g a b)) → f = g

theorem no_binopDeterminedFailure : ¬ BinopDeterminedFailure := by
  intro h
  obtain ⟨f, g, h1, h2, h3, h4, hne⟩ :=
    order_does_not_determine_binop (α := M3) (x := M3.a) (y := M3.b) (by decide)
  exact hne (h M3 inferInstance M3.a M3.b (by decide) f g h1 h2 h3 h4)

/-- Failure of a **strong** claim: the closure laws would suffice to define
reflection. Refuted by the pair `id` / `⊤`. -/
def ClosureDeterminesReflectionFailure : Prop :=
  ∀ (α : Type) (_ : PartialOrder α) (_ : OrderTop α) (c d : ClosureOperator α), c = d

theorem no_closureDeterminesReflectionFailure : ¬ ClosureDeterminesReflectionFailure := by
  intro h
  obtain ⟨c, d, hne⟩ :=
    closure_laws_do_not_determine_reflection (α := M3) (x := M3.a) (by decide)
  exact hne (h M3 inferInstance inferInstance c d)

/-- Failure of a **strong** claim: reflectors are closed under composition.
Refuted by the noncommuting pair on the chain. -/
def ReflectorCompositionClosedFailure : Prop :=
  ∀ x : Fin 4, dOp (cOp (dOp (cOp x))) = dOp (cOp x)

theorem no_reflectorCompositionClosedFailure : ¬ ReflectorCompositionClosedFailure := by
  intro h
  obtain ⟨x, hx⟩ := comp_not_idempotent
  exact hx (h x)

/-! ### N6: the logic of conditions -/

/-- Failure of a **strong** claim: a Boolean carrier would give a
distributive logic of conditions. Refuted by the v0.27 witness. -/
def DistributiveLogicFailure : Prop :=
  B3.conj 129 (B3.disj 130 132) = B3.disj (B3.conj 129 130) (B3.conj 129 132)

theorem no_distributiveLogicFailure : ¬ DistributiveLogicFailure := B3.not_distributive

/-- Failure of a **strong** claim: implication is always point-valued (the
logic is Heyting). Refuted by an antichain of three solutions. -/
def HeytingFailure : Prop := (B3.impAntichain 129 128).length = 1

theorem no_heytingFailure : ¬ HeytingFailure := by
  intro h
  unfold HeytingFailure at h
  rw [B3.implication_not_singleton] at h
  exact absurd h (by decide)

/-- Failure of a **strong** claim: public behaviour would classify source
admissibility. Refuted by the v0.28 mimic. -/
def PublicClassificationFailure : Prop :=
  ∀ f g : Nuisance.St → Bool,
    (∀ a : Bool, f (a, true) = g (a, true)) → Nuisance.Descends f → Nuisance.Descends g

theorem no_publicClassificationFailure : ¬ PublicClassificationFailure := by
  intro h
  obtain ⟨f, g, hpub, hf, hg⟩ := Nuisance.public_behaviour_does_not_classify
  exact hg (h f g hpub hf)

/-! ### N7: theory space -/

/-- Failure of a **strong** claim: provability would coincide with source
admissibility. -/
def ProvEqAdmFailure : Prop :=
  ∀ (m : TheorySpace.Mode) (b : TheorySpace.Branch), TheorySpace.prov m b = TheorySpace.adm m b

theorem no_provEqAdmFailure : ¬ ProvEqAdmFailure := by
  intro h
  obtain ⟨m, b, hne⟩ := TheorySpace.prov_ne_adm
  exact hne (h m b)

/-- Failure of a **strong** claim: a total correct truth predicate of the
same language exists. Refuted by the Tarski barrier. -/
def TotalTruthFailure : Prop :=
  ∃ (D : DiagonalSystem) (Truth : D.Sent → Prop) (A : D.Form) (neg : D.Form → D.Form),
    (∀ (φ : D.Form) (n : ℕ), Truth (D.app (neg φ) n) ↔ ¬ Truth (D.app φ n)) ∧
    (∀ σ : D.Sent, Truth (D.app A (D.code σ)) ↔ Truth σ)

theorem no_totalTruthFailure : ¬ TotalTruthFailure := by
  rintro ⟨D, Truth, A, neg, hneg, hA⟩
  exact no_total_truth_predicate D Truth A neg hneg hA

/-! ### N8: descent -/

/-- Failure: a complete cover does not recover the space. -/
def DescentFailure {Q : Type} (C : Cover Q) : Prop :=
  C.Covers ∧ ¬ Function.Bijective C.eta

theorem no_descentFailure {Q : Type} (C : Cover Q) : ¬ DescentFailure C := by
  rintro ⟨hcov, hbij⟩
  exact hbij (C.eta_bijective hcov)

/-- Failure of a **strong** claim: the quotient by dynamic arrows would
coincide with the semantic one. Refuted by an orbit in the latent world. -/
def DynamicColimitFailure : Prop :=
  ∀ (N : Machine.{0}) (x : N.St) (w : List N.Act), N.Indist x (N.transport w x)

theorem no_dynamicColimitFailure : ¬ DynamicColimitFailure := by
  intro h
  obtain ⟨N, x, w, hne⟩ := naive_dynamic_colimit_wrong
  exact hne (h N x w)

/-- Failure of a **strong** claim: a cover of states would imply a cover of
pairs. Refuted by a two-point cover. -/
def TupleCoverFailure : Prop :=
  ∀ (Q : Type) (C : Cover Q), C.Covers → ∀ p q : Q, ∃ i, p ∈ C.chart i ∧ q ∈ C.chart i

theorem no_tupleCoverFailure : ¬ TupleCoverFailure := by
  intro h
  obtain ⟨Q, C, hcov, p, q, hno⟩ := state_cover_not_tuple_cover
  obtain ⟨i, hi⟩ := h Q C hcov p q
  exact hno i hi

/-! ### The M7 summary audit -/

/-- The axes of the ASC ladder. -/
structure LadderAudit where
  /-- The ultrametric of distinguishing depth. -/
  ascTopology : Audit.ClaimStatus
  /-- The no-go for global nonexpansiveness. -/
  collapseBridge : Audit.ClaimStatus
  /-- Universal synthesis. -/
  universalSynthesis : Audit.ClaimStatus
  /-- The reflection theorem and the adjunction. -/
  reflection : Audit.ClaimStatus
  /-- Saturation of a composition of reflectors. -/
  reflectorSaturation : Audit.ClaimStatus
  /-- The lattice of conditions and its non-distributivity. -/
  constraintLogic : Audit.ClaimStatus
  /-- The diagonal lemma and the Tarski barrier. -/
  diagonalBoundary : Audit.ClaimStatus
  /-- Čech reconstruction. -/
  descent : Audit.ClaimStatus
  /-- Strong: the order determines a binary operation. -/
  binopDetermined : Audit.ClaimStatus
  /-- Strong: closures determine reflection. -/
  closureDeterminesReflection : Audit.ClaimStatus
  /-- Strong: reflectors are closed under composition. -/
  reflectorsClosed : Audit.ClaimStatus
  /-- Strong: a Boolean carrier gives a distributive logic. -/
  distributiveLogic : Audit.ClaimStatus
  /-- Strong: the logic is Heyting. -/
  heyting : Audit.ClaimStatus
  /-- Strong: public behaviour classifies source admissibility. -/
  publicClassification : Audit.ClaimStatus
  /-- Strong: provability equals admissibility. -/
  provEqAdm : Audit.ClaimStatus
  /-- Strong: a total truth predicate exists. -/
  totalTruth : Audit.ClaimStatus
  /-- Strong: the dynamic colimit equals the semantic quotient. -/
  dynamicColimit : Audit.ClaimStatus

/-- The current classification of the ASC ladder: eight proved axes and nine
refuted strong claims. -/
def ladderAudit : LadderAudit where
  ascTopology := Audit.ClaimStatus.proved
  collapseBridge := Audit.ClaimStatus.proved
  universalSynthesis := Audit.ClaimStatus.proved
  reflection := Audit.ClaimStatus.proved
  reflectorSaturation := Audit.ClaimStatus.proved
  constraintLogic := Audit.ClaimStatus.proved
  diagonalBoundary := Audit.ClaimStatus.proved
  descent := Audit.ClaimStatus.proved
  binopDetermined := Audit.ClaimStatus.refuted
  closureDeterminesReflection := Audit.ClaimStatus.refuted
  reflectorsClosed := Audit.ClaimStatus.refuted
  distributiveLogic := Audit.ClaimStatus.refuted
  heyting := Audit.ClaimStatus.refuted
  publicClassification := Audit.ClaimStatus.refuted
  provEqAdm := Audit.ClaimStatus.refuted
  totalTruth := Audit.ClaimStatus.refuted
  dynamicColimit := Audit.ClaimStatus.refuted

/-- **The final audit theorem for the ASC ladder.** Every encoded failure
mode is closed. -/
theorem ladder_audit_passes :
    (¬ UltrametricFailure latentMachine) ∧
    (¬ LipschitzFailure latentMachine) ∧
    (¬ NonexpansiveNonDiscreteFailure) ∧
    (¬ SynthesisAssocFailure) ∧
    (¬ BinopDeterminedFailure) ∧
    (¬ ClosureDeterminesReflectionFailure) ∧
    (¬ ReflectorCompositionClosedFailure) ∧
    (¬ DistributiveLogicFailure) ∧
    (¬ HeytingFailure) ∧
    (¬ PublicClassificationFailure) ∧
    (¬ ProvEqAdmFailure) ∧
    (¬ TotalTruthFailure) ∧
    (¬ DynamicColimitFailure) ∧
    (¬ TupleCoverFailure) ∧
    (∀ {Q : Type} (C : Cover Q), ¬ DescentFailure C) :=
  ⟨no_ultrametricFailure latentMachine,
   no_lipschitzFailure latentMachine,
   no_nonexpansiveNonDiscreteFailure,
   no_synthesisAssocFailure,
   no_binopDeterminedFailure,
   no_closureDeterminesReflectionFailure,
   no_reflectorCompositionClosedFailure,
   no_distributiveLogicFailure,
   no_heytingFailure,
   no_publicClassificationFailure,
   no_provEqAdmFailure,
   no_totalTruthFailure,
   no_dynamicColimitFailure,
   no_tupleCoverFailure,
   fun C => no_descentFailure C⟩

end AuditM7

end MetaLang
