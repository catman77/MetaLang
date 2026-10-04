import MetaLang.AuditM9
import MetaLang.AtlasCocycle
import MetaLang.Gluing
import MetaLang.ReflectionTheory
import MetaLang.JointReflection
import MetaLang.ConditionLogic
import MetaLang.FilterLogic
import MetaLang.TheoryPresentation
import MetaLang.BoundaryObject
import MetaLang.GrammarGrowth
import MetaLang.SourceFilterLogic
import MetaLang.LanguageGrowth

/-!
# Audit of the backlog milestones (M10–M17)

A continuation of `AuditM7`, `AuditM8` and `AuditM9` covering the milestones
of [`PRD_BACKLOG.md`](../PRD_BACKLOG.md). The module grows as milestones are
closed; each milestone has its own summary theorem.
-/

namespace MetaLang

namespace AuditBacklog

open Machine Witnesses Witnesses.GroupWitness Globalized DihedralGroup

/-! ## M12 — the remainder of the meaning algebra (v0.22–v0.24) -/

/-- Failure: the transitions of a gauge atlas violate the cocycle law. -/
def CocycleFailure : Prop :=
  ∃ (Q : Type) (A : GaugeAtlas Q) (i j k : A.ι) (a : A.C i),
    A.g j k (A.g i j a) ≠ A.g i k a

theorem no_cocycleFailure : ¬ CocycleFailure := by
  rintro ⟨Q, A, i, j, k, a, h⟩
  exact h (A.g_cocycle i j k a)

/-- Failure: a transition is not a homomorphism of the signature. -/
def TransitionHomFailure : Prop :=
  ∃ (Q : Type) (A : GaugeAtlas Q) (i j : A.ι), ¬ (A.sig i).Hom (A.sig j) (A.g i j)

theorem no_transitionHomFailure : ¬ TransitionHomFailure := by
  rintro ⟨Q, A, i, j, h⟩
  exact h (A.g_hom i j)

/-- Failure: an operation glued from partial charts loses ASC-continuity. -/
def GlobalizedContinuityFailure : Prop :=
  ¬ (shiftMachine (DihedralGroup 3)).FiltrationCompat₂
      (opAtlas (DihedralGroup 3) (gplus (G := DihedralGroup 3))).glue

theorem no_globalizedContinuityFailure : ¬ GlobalizedContinuityFailure := by
  intro h
  exact h (gplus_continuous_after_globalization (DihedralGroup 3))

/-- Failure: synthesis is not expressible through the continuation language. -/
def SynthesisPathsFailure : Prop :=
  ∃ x y z : Bow,
    ¬ (IsSynthesis x y z ↔
        ((RefinementInterface.sys Bow).refines x z ∧
         (RefinementInterface.sys Bow).refines y z ∧
         ∀ w : Bow, (RefinementInterface.sys Bow).refines x w →
           (RefinementInterface.sys Bow).refines y w →
           (RefinementInterface.sys Bow).refines z w))

theorem no_synthesisPathsFailure : ¬ SynthesisPathsFailure := by
  rintro ⟨x, y, z, h⟩
  exact h (RefinementInterface.isSynthesis_iff_paths x y z)

/-- Failure: relabelling by an observer changes the synthesis. -/
def ObserverSynthesisFailure : Prop :=
  ∃ (α β : Type) (_ : PartialOrder α) (_ : PartialOrder β) (e : α ≃o β) (x y z : α),
    IsSynthesis x y z ∧ ¬ IsSynthesis (e x) (e y) (e z)

theorem no_observerSynthesisFailure : ¬ ObserverSynthesisFailure := by
  rintro ⟨α, β, _, _, e, x, y, z, hs, h⟩
  exact h (isSynthesis_orderIso e hs)

/-- Failure: relabelling by an observer changes the contrast antichain. -/
def ObserverContrastFailure : Prop :=
  ∃ (α β : Type) (_ : Lattice α) (_ : Lattice β) (e : α ≃o β) (x y : α),
    Contrast (e x) (e y) ≠ e '' Contrast x y

theorem no_observerContrastFailure : ¬ ObserverContrastFailure := by
  rintro ⟨α, β, _, _, e, x, y, h⟩
  exact h (contrast_orderIso e x y)

/-- Failure: synthesis is not total on a lattice. -/
def LatticeSynthesisFailure : Prop :=
  ∃ (α : Type) (_ : Lattice α) (x y : α), ¬ IsSynthesis x y (x ⊔ y)

theorem no_latticeSynthesisFailure : ¬ LatticeSynthesisFailure := by
  rintro ⟨α, _, x, y, h⟩
  exact h (lattice_total_synthesis x y)

/-- Failure: the contrast is empty on a finite lattice. -/
def ContrastEmptyFailure : Prop :=
  ∃ (α : Type) (_ : Lattice α) (_ : Finite α) (x y : α), Contrast x y = ∅

theorem no_contrastEmptyFailure : ¬ ContrastEmptyFailure := by
  rintro ⟨α, _, _, x, y, h⟩
  obtain ⟨z, hz⟩ := contrast_nonempty x y
  rw [h] at hz
  exact hz

/-- Failure of the **strong** claim: the order of continuations could single
out a unique total monotone operation. Refuted by the projections. -/
def BinopIdentifiedFailure : Prop :=
  ∀ (f g : Bool → Bool → Bool),
    (∀ a b a' b' : Bool, a ≤ a' → b ≤ b' → f a b ≤ f a' b') →
    (∀ a b a' b' : Bool, a ≤ a' → b ≤ b' → g a b ≤ g a' b') →
    f = g

theorem no_binopIdentifiedFailure : ¬ BinopIdentifiedFailure := by
  intro h
  obtain ⟨f, g, hf, hg, hne⟩ :=
    binop_not_identified_by_order (α := Bool) (x := false) (y := true) (by decide)
  exact hne (congrFun (congrFun (h f g hf hg) false) true)

/-- **The M12 audit passes.** Nine failure modes are closed: eight positive
theorems and one refutation of a strong claim. -/
theorem m12_audit_passes :
    (¬ CocycleFailure) ∧
    (¬ TransitionHomFailure) ∧
    (¬ GlobalizedContinuityFailure) ∧
    (¬ SynthesisPathsFailure) ∧
    (¬ ObserverSynthesisFailure) ∧
    (¬ ObserverContrastFailure) ∧
    (¬ LatticeSynthesisFailure) ∧
    (¬ ContrastEmptyFailure) ∧
    (¬ BinopIdentifiedFailure) :=
  ⟨no_cocycleFailure,
   no_transitionHomFailure,
   no_globalizedContinuityFailure,
   no_synthesisPathsFailure,
   no_observerSynthesisFailure,
   no_observerContrastFailure,
   no_latticeSynthesisFailure,
   no_contrastEmptyFailure,
   no_binopIdentifiedFailure⟩

/-! ## M11 — topology, gluing, behavioural descent (v0.18–v0.21) -/

/-- Failure: transport along a word of length `k` stretches the distance by more than `2^k`. -/
def WordBoundFailure : Prop :=
  ∃ (M : Machine.{0}) (w : List M.Act) (x y : M.St),
    ¬ (M.dASC (M.transport w x) (M.transport w y) ≤
        (2 : ℝ) ^ (w.length : ℤ) * M.dASC x y)

theorem no_wordBoundFailure : ¬ WordBoundFailure := by
  rintro ⟨M, w, x, y, h⟩
  exact h (Machine.dASC_transport_le w x y)

/-- Failure: a single primitive stretches the distance by more than a factor of two. -/
def TwoLipschitzFailure : Prop :=
  ∃ (M : Machine.{0}) (a : M.Act) (x y : M.St),
    ¬ (M.dASC (M.T a x) (M.T a y) ≤ 2 * M.dASC x y)

theorem no_twoLipschitzFailure : ¬ TwoLipschitzFailure := by
  rintro ⟨M, a, x, y, h⟩
  exact h (Machine.dASC_step_le a x y)

/-- Failure: with a single idempotent generator the refinement does not
collapse at depth 1. -/
def SingleGeneratorFailure : Prop :=
  ∃ (M : Machine.{0}) (h : Machine.SingleGenerator M) (x y : M.St),
    ¬ (M.Indist x y ↔ M.approx 1 x y)

theorem no_singleGeneratorFailure : ¬ SingleGeneratorFailure := by
  rintro ⟨M, h, x, y, hne⟩
  exact hne (h.indist_iff_approx_one x y)

/-- Failure: the local filtration of a chart diverges from the global one. -/
def LocalFiltrationFailure : Prop :=
  ∃ (M : Machine.{0}) (C : Subchart M) (n : ℕ) (x y : C.machine.St),
    ¬ (C.machine.approx n x y ↔ M.approx n x.1 y.1)

theorem no_localFiltrationFailure : ¬ LocalFiltrationFailure := by
  rintro ⟨M, C, n, x, y, h⟩
  exact h (C.approx_iff n x y)

/-- Failure: the distinguishing depth inside a chart diverges from the global one. -/
def LocalDepthFailure : Prop :=
  ∃ (M : Machine.{0}) (C : Subchart M) (x y : C.machine.St),
    C.machine.sep x y ≠ M.sep x.1 y.1

theorem no_localDepthFailure : ¬ LocalDepthFailure := by
  rintro ⟨M, C, x, y, h⟩
  exact h (C.sep_eq x y)

/-- Failure: the semantics is not recovered from a cover by charts. -/
def ChartReconstructionFailure : Prop :=
  ∃ (M : Machine.{0}) (A : Machine.ChartAtlas.{0} M) (x y : M.St),
    ¬ (M.Indist x y ↔
        ∃ (i : A.ι) (hx : x ∈ (A.chart i).carrier) (hy : y ∈ (A.chart i).carrier),
          (A.chart i).machine.Indist ⟨x, hx⟩ ⟨y, hy⟩)

theorem no_chartReconstructionFailure : ¬ ChartReconstructionFailure := by
  rintro ⟨M, A, x, y, h⟩
  exact h (Machine.indist_from_charts A x y)

/-- Failure: a grammar expansion does not refine the topology. -/
def GrammarRefineFailure : Prop :=
  ∃ (E : Expansion.{0}) (n : ℕ) (x y : E.St),
    E.full.approx n x y ∧ ¬ E.base.approx n x y

theorem no_grammarRefineFailure : ¬ GrammarRefineFailure := by
  rintro ⟨E, n, x, y, hf, h⟩
  exact h (Expansion.approx_full_imp_base n x y hf)

/-- Failure: adding a synonym refines the topology. -/
def SynonymStrictFailure : Prop :=
  ∃ (E : Expansion.{0})
    (_ : ∀ b : E.Act₁, ∃ a : E.Act₀, ∀ x : E.St, E.T b x = E.T (E.emb a) x)
    (n : ℕ) (x y : E.St), E.base.approx n x y ∧ ¬ E.full.approx n x y

theorem no_synonymStrictFailure : ¬ SynonymStrictFailure := by
  rintro ⟨E, hsyn, n, x, y, hb, h⟩
  exact h (Expansion.approx_base_imp_full hsyn n x y hb)

/-- Failure: at some depth there is no activation witness. -/
def ActivationWitnessFailure : Prop :=
  ∃ n : ℕ, ∀ x y : ℕ → Bool, (shiftMachine Bool).sep x y ≠ n

theorem no_activationWitnessFailure : ¬ ActivationWitnessFailure := by
  rintro ⟨n, h⟩
  obtain ⟨x, y, hxy⟩ := Multiscale.exists_sep_eq n
  exact h x y hxy

/-- Failure: a spectator presentation is not coequalized. -/
def SpectatorFailure : Prop :=
  ∃ (M : Machine.{0}) (B : Type) (x : M.St) (b b' : B),
    ¬ (Spectator.machine M B).Indist (x, b) (x, b')

theorem no_spectatorFailure : ¬ SpectatorFailure := by
  rintro ⟨M, B, x, b, b', h⟩
  exact h (Spectator.spectator_collapsed B x b b')

/-- Failure of the **strong** claim: a grammar expansion could never be
strict. Refuted by a witness. -/
def ExpansionNeverStrictFailure : Prop :=
  GrammarWitness.strictExp.full.Indist 0 1

theorem no_expansionNeverStrictFailure : ¬ ExpansionNeverStrictFailure :=
  GrammarWitness.full_separates_zero_one

/-- Failure of the **strong** claim: the continuation scale could not
decrease for semantically distinct states. Refuted by the infinite
witness. -/
def ScaleCollapseFailure : Prop :=
  ∃ n : ℕ, ∀ x y : ℕ → Bool,
    ¬ (shiftMachine Bool).Indist x y →
      (2 : ℝ) ^ (-(n : ℤ)) < (shiftMachine Bool).dASC x y

theorem no_scaleCollapseFailure : ¬ ScaleCollapseFailure := by
  rintro ⟨n, h⟩
  obtain ⟨x, y, hne, hd⟩ := Multiscale.scales_separate n
  exact absurd (h x y hne) (by rw [hd]; exact lt_irrefl _)

/-- Failure of the **strong** claim: depth 0 could suffice for descent. -/
def ResponseOnlySufficientFailure : Prop :=
  ∀ x y : Fin 4, Separation.depthMachine.approx 0 x y → Separation.depthMachine.Indist x y

theorem no_responseOnlySufficientFailure : ¬ ResponseOnlySufficientFailure := by
  intro h
  exact DescentDepth.response_only_breaks_descent.2
    (h 0 1 DescentDepth.response_only_breaks_descent.1)

/-- Failure of the **strong** claim: depth 1 could suffice for descent. -/
def OneRoundSufficientFailure : Prop :=
  ∀ x y : Fin 4, Separation.depthMachine.approx 1 x y → Separation.depthMachine.Indist x y

theorem no_oneRoundSufficientFailure : ¬ OneRoundSufficientFailure := by
  intro h
  exact DescentDepth.one_round_insufficient.2
    (h 1 3 DescentDepth.one_round_insufficient.1)

/-- **The M11 audit passes.** Fourteen failure modes are closed: ten
positive theorems and four refutations of strong claims. -/
theorem m11_audit_passes :
    (¬ WordBoundFailure) ∧
    (¬ TwoLipschitzFailure) ∧
    (¬ SingleGeneratorFailure) ∧
    (¬ LocalFiltrationFailure) ∧
    (¬ LocalDepthFailure) ∧
    (¬ ChartReconstructionFailure) ∧
    (¬ GrammarRefineFailure) ∧
    (¬ SynonymStrictFailure) ∧
    (¬ ActivationWitnessFailure) ∧
    (¬ SpectatorFailure) ∧
    (¬ ExpansionNeverStrictFailure) ∧
    (¬ ScaleCollapseFailure) ∧
    (¬ ResponseOnlySufficientFailure) ∧
    (¬ OneRoundSufficientFailure) :=
  ⟨no_wordBoundFailure,
   no_twoLipschitzFailure,
   no_singleGeneratorFailure,
   no_localFiltrationFailure,
   no_localDepthFailure,
   no_chartReconstructionFailure,
   no_grammarRefineFailure,
   no_synonymStrictFailure,
   no_activationWitnessFailure,
   no_spectatorFailure,
   no_expansionNeverStrictFailure,
   no_scaleCollapseFailure,
   no_responseOnlySufficientFailure,
   no_oneRoundSufficientFailure⟩

/-! ## M13a — the theory of reflection (v0.25) -/

/-- Failure: the reflection relation is not recovered from behaviour and `F`. -/
def ReflectionPathsFailure : Prop :=
  ∃ (F : Set Bow) (x y : Bow),
    ¬ (IsReflectionAt F x y ↔
        (y ∈ F ∧ (RefinementInterface.sys Bow).refines x y ∧
          ∀ z ∈ F, (RefinementInterface.sys Bow).refines x z →
            (RefinementInterface.sys Bow).refines y z))

theorem no_reflectionPathsFailure : ¬ ReflectionPathsFailure := by
  rintro ⟨F, x, y, h⟩
  exact h (isReflectionAt_iff_paths F x y)

/-- Failure: the principal reflection differs from `κ ⊔ x`. -/
def PrincipalReflectionFailure : Prop :=
  ∃ (α : Type) (_ : Lattice α) (κ x : α), ¬ IsReflectionAt {z : α | κ ≤ z} x (κ ⊔ x)

theorem no_principalReflectionFailure : ¬ PrincipalReflectionFailure := by
  rintro ⟨α, _, κ, x, h⟩
  exact h (principal_isReflectionAt κ x)

/-- Failure: reflection does not preserve universal synthesis. -/
def SynthesisPreservationFailure : Prop :=
  ∃ (α : Type) (_ : PartialOrder α) (F : Set α) (h : Reflective F) (x y z : α),
    IsSynthesis x y z ∧
      ¬ IsLeast {f | f ∈ F ∧ rho h x ≤ f ∧ rho h y ≤ f} (rho h z)

theorem no_synthesisPreservationFailure : ¬ SynthesisPreservationFailure := by
  rintro ⟨α, _, F, h, x, y, z, hz, hne⟩
  exact hne (rho_preserves_synthesis h hz)

/-- Failure of the **strong** claim: reflection could always be
single-valued. Refuted by the non-reflective pair of diamond atoms. -/
def ReflectionAlwaysPointFailure : Prop :=
  ∀ y y' : M3, y ∈ Ref NonReflective.F M3.bot → y' ∈ Ref NonReflective.F M3.bot → y = y'

theorem no_reflectionAlwaysPointFailure : ¬ ReflectionAlwaysPointFailure := by
  intro h
  obtain ⟨ha, hb, hne⟩ := NonReflective.ref_bot_antichain
  exact hne (h M3.a M3.b ha hb)

/-- Failure of the **strong** claim: a forced choice of one point of the
antichain could preserve the adjunction. -/
def ForcedChoiceFailure : Prop :=
  ∀ (x : M3), ∀ f ∈ NonReflective.F, (fun _ : M3 => M3.a) x ≤ f ↔ x ≤ f

theorem no_forcedChoiceFailure : ¬ ForcedChoiceFailure :=
  NonReflective.forced_choice_breaks_adjunction (fun _ => M3.a) rfl

/-- Failure: the reflection of the infinite Boolean witness is not 1-Lipschitz. -/
def InfiniteReflectionLipschitzFailure : Prop :=
  ∃ A : ℕ → Bool,
    ¬ (shiftMachine Bool).FiltrationCompat₁ (Witnesses.InfiniteReflection.refl A)

theorem no_infiniteReflectionLipschitzFailure : ¬ InfiniteReflectionLipschitzFailure := by
  rintro ⟨A, h⟩
  exact h (InfiniteReflectionASC.refl_filtrationCompat A)

/-- **The M13a audit passes.** Six failure modes are closed: four positive
theorems and two refutations of strong claims. -/
theorem m13a_audit_passes :
    (¬ ReflectionPathsFailure) ∧
    (¬ PrincipalReflectionFailure) ∧
    (¬ SynthesisPreservationFailure) ∧
    (¬ ReflectionAlwaysPointFailure) ∧
    (¬ ForcedChoiceFailure) ∧
    (¬ InfiniteReflectionLipschitzFailure) :=
  ⟨no_reflectionPathsFailure,
   no_principalReflectionFailure,
   no_synthesisPreservationFailure,
   no_reflectionAlwaysPointFailure,
   no_forcedChoiceFailure,
   no_infiniteReflectionLipschitzFailure⟩

/-! ## M13b — the algebra of reflectors (v0.26) -/

/-- Failure: independent reflectors do not commute. -/
def IndependentCommuteFailure : Prop :=
  ∃ (β γ : Type) (_ : PartialOrder β) (_ : PartialOrder γ)
    (c : ClosureOperator β) (d : ClosureOperator γ) (p : β × γ),
    leftOp c (rightOp d p) ≠ rightOp d (leftOp c p)

theorem no_independentCommuteFailure : ¬ IndependentCommuteFailure := by
  rintro ⟨β, γ, _, _, c, d, p, h⟩
  exact h (independent_commute c d p)

/-- Failure: the composite of independent reflectors is not idempotent. -/
def IndependentJointFailure : Prop :=
  ∃ (β γ : Type) (_ : PartialOrder β) (_ : PartialOrder γ)
    (c : ClosureOperator β) (d : ClosureOperator γ) (p : β × γ),
    leftOp c (rightOp d (leftOp c (rightOp d p))) ≠ leftOp c (rightOp d p)

theorem no_independentJointFailure : ¬ IndependentJointFailure := by
  rintro ⟨β, γ, _, _, c, d, p, h⟩
  exact h (independent_comp_idempotent c d p)

/-- Failure of the **strong** claim: commuting could require independence.
Refuted by an operator that commutes with itself. -/
def CommuteRequiresIndependenceFailure : Prop :=
  ∀ c d : ClosureOperator (Fin 4), (∀ x, c (d x) = d (c x)) →
    ∀ x, (c x = x ↔ d x = x) → c x = x

theorem no_commuteRequiresIndependenceFailure : ¬ CommuteRequiresIndependenceFailure := by
  intro h
  obtain ⟨c, d, hcomm, hfix, x, hx⟩ := commute_without_independence
  exact hx (h c d hcomm x (hfix x))

/-- Failure of the **strong** claim: some single-pass order would always
give a joint reflector. Refuted by the feedback pair on the chain
`Fin 5`. -/
def OnePassAlwaysJointFailure : Prop :=
  Feedback.C (Feedback.D 0) = 4 ∨ Feedback.D (Feedback.C 0) = 4

theorem no_onePassAlwaysJointFailure : ¬ OnePassAlwaysJointFailure := by
  rintro (h | h)
  · exact Feedback.neither_order_is_joint.1 h
  · exact Feedback.neither_order_is_joint.2 h

/-- Failure of the **strong** claim: iteration is never needed. -/
def NoIterationNeededFailure : Prop :=
  iter (fun x => Feedback.C (Feedback.D x)) 1 0 = 4

theorem no_noIterationNeededFailure : ¬ NoIterationNeededFailure :=
  Feedback.iteration_needed.1

/-- Failure: saturation depends on the order. -/
def SaturationOrderFailure : Prop :=
  iter (fun x => Feedback.C (Feedback.D x)) 2 0 ≠
    iter (fun x => Feedback.D (Feedback.C x)) 2 0

theorem no_saturationOrderFailure : ¬ SaturationOrderFailure := by
  intro h
  exact h (Feedback.saturation_both_orders.1.trans Feedback.saturation_both_orders.2.symm)

/-- Failure: the composite of infinite reflections is not a reflector into
the intersection of the subspaces. -/
def InfiniteJointFailure : Prop :=
  ∃ A B : ℕ → Bool,
    Witnesses.InfiniteReflection.Target (fun i => A i || B i) ≠
      Witnesses.InfiniteReflection.Target A ∩ Witnesses.InfiniteReflection.Target B

theorem no_infiniteJointFailure : ¬ InfiniteJointFailure := by
  rintro ⟨A, B, h⟩
  exact h (InfiniteJoint.joint_target A B)

/-- Failure: the composite of infinite reflections is not ASC-continuous. -/
def InfiniteCompContinuityFailure : Prop :=
  ∃ A B : ℕ → Bool,
    ¬ (shiftMachine Bool).FiltrationCompat₁
        (fun x => Witnesses.InfiniteReflection.refl A
          (Witnesses.InfiniteReflection.refl B x))

theorem no_infiniteCompContinuityFailure : ¬ InfiniteCompContinuityFailure := by
  rintro ⟨A, B, h⟩
  exact h (InfiniteJoint.comp_filtrationCompat A B)

/-- **The M13b audit passes.** Eight failure modes are closed: five positive
theorems and three refutations of strong claims. -/
theorem m13b_audit_passes :
    (¬ IndependentCommuteFailure) ∧
    (¬ IndependentJointFailure) ∧
    (¬ CommuteRequiresIndependenceFailure) ∧
    (¬ OnePassAlwaysJointFailure) ∧
    (¬ NoIterationNeededFailure) ∧
    (¬ SaturationOrderFailure) ∧
    (¬ InfiniteJointFailure) ∧
    (¬ InfiniteCompContinuityFailure) :=
  ⟨no_independentCommuteFailure,
   no_independentJointFailure,
   no_commuteRequiresIndependenceFailure,
   no_onePassAlwaysJointFailure,
   no_noIterationNeededFailure,
   no_saturationOrderFailure,
   no_infiniteJointFailure,
   no_infiniteCompContinuityFailure⟩

/-! ## M13c — the abstract logic of conditions (v0.27, order-theoretic part) -/

/-- Failure: entailment of conditions diverges from the reverse order of reflectors. -/
def EntailmentOrderFailure : Prop :=
  ∃ (α : Type) (_ : PartialOrder α) (c d : ClosureOperator α),
    ¬ (Entails c d ↔ ∀ x : α, d x ≤ c x)

theorem no_entailmentOrderFailure : ¬ EntailmentOrderFailure := by
  rintro ⟨α, _, c, d, h⟩
  exact h (entails_iff_reverse_order c d)

/-- Failure: absorption with the hull disjunction fails. -/
def AbsorptionFailure : Prop :=
  ∃ (α : Type) (_ : Lattice α) (h : ClosureOperator α) (x y : α), x ⊓ h (x ⊔ y) ≠ x

theorem no_absorptionFailure : ¬ AbsorptionFailure := by
  rintro ⟨α, _, h, x, y, hne⟩
  exact hne (absorption_of_closure h x y)

/-- Failure: the implication antichain loses a solution. -/
def ResidualCompleteFailure : Prop :=
  ∃ (α : Type) (_ : Lattice α) (_ : Finite α) (x y z : α),
    x ⊓ z ≤ y ∧ ¬ ∃ m ∈ ImpAntichain x y, z ≤ m

theorem no_residualCompleteFailure : ¬ ResidualCompleteFailure := by
  rintro ⟨α, _, _, x, y, z, hz, h⟩
  exact h (impAntichain_complete x y z hz)

/-- Failure: with a singleton antichain, residuation is not exact. -/
def SingletonResiduationFailure : Prop :=
  ∃ (α : Type) (_ : Lattice α) (_ : Finite α) (x y m : α),
    ImpAntichain x y = {m} ∧ ∃ z, ¬ (x ⊓ z ≤ y ↔ z ≤ m)

theorem no_singletonResiduationFailure : ¬ SingletonResiduationFailure := by
  rintro ⟨α, _, _, x, y, m, hm, z, h⟩
  exact h (residuation_of_singleton hm z)

/-- Failure of the **strong** claim: implication could always be
single-valued. Refuted by the diamond. -/
def ImplicationSingleValuedFailure : Prop :=
  ∀ u v : M3, u ∈ ImpAntichain M3.a M3.bot → v ∈ ImpAntichain M3.a M3.bot → u = v

theorem no_implicationSingleValuedFailure : ¬ ImplicationSingleValuedFailure := by
  intro h
  obtain ⟨hb, hc, hne⟩ := DiamondLogic.impAntichain_multivalued
  exact hne (h M3.b M3.c hb hc)

/-- Failure of the **strong** claim: negation could always be
single-valued. -/
def NegationSingleValuedFailure : Prop :=
  ¬ ∃ u v : M3,
      u ∈ ImpAntichain M3.a M3.bot ∧ v ∈ ImpAntichain M3.a M3.bot ∧ u ≠ v

theorem no_negationSingleValuedFailure : ¬ NegationSingleValuedFailure := by
  intro h
  exact h DiamondLogic.negation_multivalued

/-- **The M13c audit passes.** Six failure modes are closed: four positive
theorems and two refutations of strong claims. -/
theorem m13c_audit_passes :
    (¬ EntailmentOrderFailure) ∧
    (¬ AbsorptionFailure) ∧
    (¬ ResidualCompleteFailure) ∧
    (¬ SingletonResiduationFailure) ∧
    (¬ ImplicationSingleValuedFailure) ∧
    (¬ NegationSingleValuedFailure) :=
  ⟨no_entailmentOrderFailure,
   no_absorptionFailure,
   no_residualCompleteFailure,
   no_singletonResiduationFailure,
   no_implicationSingleValuedFailure,
   no_negationSingleValuedFailure⟩

/-! ## M13d — non-modularity and non-classical families (v0.27, in part) -/

/-- Failure of the **strong** claim: the logic of conditions of `B3` could
be modular. -/
def B3ModularFailure : Prop :=
  B3.disj 130 (B3.conj 132 131) = B3.conj (B3.disj 130 132) 131

theorem no_b3ModularFailure : ¬ B3ModularFailure :=
  B3.not_modular.2.2.2.2

/-- Failure of the **strong** claim: the diamond could be distributive. -/
def M3DistributiveFailure : Prop :=
  M3.a ⊓ (M3.b ⊔ M3.c) = (M3.a ⊓ M3.b) ⊔ (M3.a ⊓ M3.c)

theorem no_m3DistributiveFailure : ¬ M3DistributiveFailure := m3_not_distributive

/-- Failure of the **strong** claim: the pentagon could be distributive. -/
def N5DistributiveFailure : Prop :=
  N5.y ⊓ (N5.x ⊔ N5.z) = (N5.y ⊓ N5.x) ⊔ (N5.y ⊓ N5.z)

theorem no_n5DistributiveFailure : ¬ N5DistributiveFailure := n5_not_distributive

/-- Failure: on a linear carrier the union of conditions stops being a
condition, i.e. the hull is needed after all. -/
def LinearHullFailure : Prop :=
  ∃ (α : Type) (_ : LinearOrder α) (_ : OrderTop α) (F G : Set α),
    IsMooreSet F ∧ IsMooreSet G ∧ ¬ IsMooreSet (F ∪ G)

theorem no_linearHullFailure : ¬ LinearHullFailure := by
  rintro ⟨α, _, _, F, G, hF, hG, h⟩
  exact h (linear_union_isMooreSet hF hG)

/-- **The M13d audit (partial) passes.** Four failure modes are closed: one
positive theorem and three refutations of strong claims. The remaining gates
of this milestone — those about the source filter grammar — are handled in
the continuation section below. -/
theorem m13d_partial_audit_passes :
    (¬ B3ModularFailure) ∧
    (¬ M3DistributiveFailure) ∧
    (¬ N5DistributiveFailure) ∧
    (¬ LinearHullFailure) :=
  ⟨no_b3ModularFailure,
   no_m3DistributiveFailure,
   no_n5DistributiveFailure,
   no_linearHullFailure⟩

/-! ## M14 — theory presentations and typed partiality (v0.29, v0.31) -/

/-- Failure: extending the axioms does not descend through the quotient of presentations. -/
def ExtensionDescentFailure : Prop :=
  ∃ (α : Type) (_ : Lattice α) (c : ClosureOperator α) (a a' b : α),
    c a = c a' ∧ c (a ⊔ b) ≠ c (a' ⊔ b)

theorem no_extensionDescentFailure : ¬ ExtensionDescentFailure := by
  rintro ⟨α, _, c, a, a', b, h, hne⟩
  exact hne (extension_descends c h b)

/-- Failure: the signature of irreducibles does not determine the theory. -/
def SignatureFailure : Prop :=
  ∃ (α : Type) (_ : Lattice α) (_ : Finite α) (a b : α),
    irredSignature a = irredSignature b ∧ a ≠ b

theorem no_signatureFailure : ¬ SignatureFailure := by
  rintro ⟨α, _, _, a, b, h, hne⟩
  exact hne (eq_of_irredSignature_eq h)

/-- Failure of the **strong** claim: a theory could have exactly one
presentation. -/
def UniquePresentationFailure : Prop :=
  ∀ a b : Fin 3, chainClosure a = chainClosure b → a = b

theorem no_uniquePresentationFailure : ¬ UniquePresentationFailure := by
  intro h
  obtain ⟨a, b, hne, heq⟩ := multiple_presentations
  exact hne (h a b heq)

/-- Failure: the interval lift loses an exact solution. -/
def IntervalSoundnessFailure : Prop :=
  ∃ (Φ : Finset Bool → Finset Bool) (I : Interval Bool) (A : Finset Bool),
    ExactFixed Φ A ∧ A ∈ gamma I ∧ A ∉ gamma (istep Φ I)

theorem no_intervalSoundnessFailure : ¬ IntervalSoundnessFailure := by
  rintro ⟨Φ, I, A, hA, hmem, h⟩
  exact h (Partial.exact_mem_gamma_istep Φ I hA hmem)

/-- Failure of the **strong** claim: a symmetric unknown could be resolved
by an equivariant choice of one branch. -/
def EquivariantTiebreakFailure : Prop :=
  ∃ (f : Interval Bool → Finset Bool) (b : Bool),
    (∀ I, f (Partial.swapI I) = (f I).image Bool.not) ∧ f fullInterval = {b}

theorem no_equivariantTiebreakFailure : ¬ EquivariantTiebreakFailure := by
  rintro ⟨f, b, hequiv, hsing⟩
  exact Partial.no_equivariant_tiebreak f hequiv b hsing

/-- Failure of the **strong** claim: the partial status could distinguish
the cause of unresolvedness. Refuted by the pair "liar / bifurcation":
different numbers of exact solutions, one and the same fully unknown
interval. -/
def PartialClassifiesCauseFailure : Prop :=
  istep Partial.bifurcated fullInterval ≠ istep liar fullInterval

theorem no_partialClassifiesCauseFailure : ¬ PartialClassifiesCauseFailure := by
  intro h
  exact h (Partial.bifurcation_indistinguishable_from_unknown.1.trans
    Partial.bifurcation_indistinguishable_from_unknown.2.symm)

/-- **The M14 audit (partial) passes.** Six failure modes are closed: three
positive theorems and three refutations of strong claims. -/
theorem m14_partial_audit_passes :
    (¬ ExtensionDescentFailure) ∧
    (¬ SignatureFailure) ∧
    (¬ UniquePresentationFailure) ∧
    (¬ IntervalSoundnessFailure) ∧
    (¬ EquivariantTiebreakFailure) ∧
    (¬ PartialClassifiesCauseFailure) :=
  ⟨no_extensionDescentFailure,
   no_signatureFailure,
   no_uniquePresentationFailure,
   no_intervalSoundnessFailure,
   no_equivariantTiebreakFailure,
   no_partialClassifiesCauseFailure⟩

/-! ## M15 — the boundary object (v0.32 §1–§2) -/

/-- Failure: the exact solutions cannot be read off the one-cycles. -/
def OneCycleFailure : Prop :=
  ∃ (Φ : Finset Bool → Finset Bool) (A : Finset Bool),
    ¬ (ExactFixed Φ A ↔ (Boundary.IsCyclic Φ A ∧ Φ A = A))

theorem no_oneCycleFailure : ¬ OneCycleFailure := by
  rintro ⟨Φ, A, h⟩
  exact h (Boundary.exact_iff_one_cycle Φ A)

/-- Failure: a point on a long cycle turns out to be a solution. -/
def CycleIsSolutionFailure : Prop :=
  ∃ (Φ : Finset Bool → Finset Bool) (A : Finset Bool),
    Boundary.IsCyclic Φ A ∧ Φ A ≠ A ∧ ExactFixed Φ A

theorem no_cycleIsSolutionFailure : ¬ CycleIsSolutionFailure := by
  rintro ⟨Φ, A, hc, hne, hex⟩
  exact Boundary.cycle_not_solution hc hne hex

/-- Failure of the **strong** claim: the partial layer could classify the
cause of unresolvedness. Refuted by the pair "liar / bifurcation". -/
def PartialLayerClassifiesFailure : Prop :=
  Boundary.fixCount liar = Boundary.fixCount Partial.bifurcated

theorem no_partialLayerClassifiesFailure : ¬ PartialLayerClassifiesFailure :=
  Boundary.unknown_has_distinct_causes.2

/-- Failure: the signatures of the five modes fail to tell them apart. -/
def ModeSignatureFailure : Prop :=
  Boundary.signature liar = Boundary.signature Partial.bifurcated ∨
  Boundary.signature Boundary.hiddenPhi = Boundary.signature constPhi ∨
  Boundary.signature idPhi = Boundary.signature Partial.bifurcated

theorem no_modeSignatureFailure : ¬ ModeSignatureFailure := by
  rintro (h | h | h)
  · exact Boundary.five_modes_distinct.2.2.1 h
  · exact Boundary.five_modes_distinct.2.2.2.2.2.2.2.2.1 h
  · exact Boundary.five_modes_distinct.2.2.2.2.2.1 h

/-- Failure of the **strong** claim: the resolved mode could coincide with
total unknownness already at the partial layer. -/
def ResolvedIsUnknownFailure : Prop :=
  istep constPhi fullInterval = fullInterval

theorem no_resolvedIsUnknownFailure : ¬ ResolvedIsUnknownFailure :=
  Boundary.resolved_ne_unknown

/-- **The M15 audit passes.** Five failure modes are closed: three positive
theorems and two refutations of strong claims. -/
theorem m15_audit_passes :
    (¬ OneCycleFailure) ∧
    (¬ CycleIsSolutionFailure) ∧
    (¬ PartialLayerClassifiesFailure) ∧
    (¬ ModeSignatureFailure) ∧
    (¬ ResolvedIsUnknownFailure) :=
  ⟨no_oneCycleFailure,
   no_cycleIsSolutionFailure,
   no_partialLayerClassifiesFailure,
   no_modeSignatureFailure,
   no_resolvedIsUnknownFailure⟩

/-! ## M16.2 — active science (v0.34) -/

/-- Failure of the **strong** claim: repeating an observer could make a
family jointly faithful. -/
def RepetitionFaithfulFailure : Prop :=
  (ShadowWitness.repeatedFamily (Fin 20)).Faithful

theorem no_repetitionFaithfulFailure : ¬ RepetitionFaithfulFailure :=
  ShadowWitness.repeated_not_faithful (Fin 20)

/-- Failure of the **strong** claim: repetition could remove a false
universal law. -/
def RepetitionRemovesShadowFailure : Prop :=
  (ShadowWitness.repeatedFamily (Fin 20)).Fundamental
    ShadowWitness.commT ShadowWitness.commU

theorem no_repetitionRemovesShadowFailure : ¬ RepetitionRemovesShadowFailure :=
  (ShadowWitness.repeated_keeps_shadow (Fin 20)).2

/-- Failure: the blind relation of the starting family turns out to be
trivial. -/
def StartBlindTrivialFailure : Prop :=
  ∀ x y : ShadowWitness.Src,
    (ShadowWitness.repeatedFamily (Fin 20)).Blind Set.univ x y → x = y

theorem no_startBlindTrivialFailure : ¬ StartBlindTrivialFailure := by
  intro h
  obtain ⟨x, y, hne, hb⟩ := ShadowWitness.repeated_blind_nontrivial (Fin 20)
  exact hne (h x y hb)

/-- Failure of the **strong** claim: the absence of false positives on a
finite grammar could certify joint faithfulness. -/
def ZeroFalsePositiveCertifiesFailure : Prop :=
  (ShadowWitness.shadowFamily.Scoped ShadowWitness.trivT ShadowWitness.trivT ∧
    ShadowWitness.shadowFamily.Fundamental ShadowWitness.trivT ShadowWitness.trivT) →
    ShadowWitness.shadowFamily.Faithful

theorem no_zeroFalsePositiveCertifiesFailure : ¬ ZeroFalsePositiveCertifiesFailure := by
  intro h
  obtain ⟨hs, hf, hnf⟩ := ShadowWitness.zero_false_positives_does_not_certify
  exact hnf (h ⟨hs, hf⟩)

/-- Failure: the set of universal laws does not shrink when an observer is
added. -/
def LawsMonotoneFailure : Prop :=
  ∃ (S : Type) (F : AlgObsFamily S) (V : Type) (t u : Term V) (I J : Set F.ι),
    I ⊆ J ∧ F.ScopedOn J t u ∧ ¬ F.ScopedOn I t u

theorem no_lawsMonotoneFailure : ¬ LawsMonotoneFailure := by
  rintro ⟨S, F, V, t, u, I, J, hsub, hJ, h⟩
  exact h (AlgObsFamily.scopedOn_antitone hsub hJ)

/-- **The M16.2 audit passes.** Five failure modes are closed: two positive
theorems and three refutations of strong claims. -/
theorem m16b_audit_passes :
    (¬ RepetitionFaithfulFailure) ∧
    (¬ RepetitionRemovesShadowFailure) ∧
    (¬ StartBlindTrivialFailure) ∧
    (¬ ZeroFalsePositiveCertifiesFailure) ∧
    (¬ LawsMonotoneFailure) :=
  ⟨no_repetitionFaithfulFailure,
   no_repetitionRemovesShadowFailure,
   no_startBlindTrivialFailure,
   no_zeroFalsePositiveCertifiesFailure,
   no_lawsMonotoneFailure⟩

/-! ## M16.3 and M17.1 — observer synthesis and grammar growth (v0.35, v0.36) -/

/-- Failure of the **strong** claim: the restricted grammar could fail to be
coarser than the full one. -/
def RestrictedAsFineFailure : Prop :=
  ∀ x y : ShadowWitness.Src,
    ShadowWitness.activeFamily.Blind GrammarGrowth.restricted x y →
      ShadowWitness.activeFamily.Blind (Set.univ : Set ShadowWitness.activeFamily.ι) x y

theorem no_restrictedAsFineFailure : ¬ RestrictedAsFineFailure := by
  intro h
  obtain ⟨x, y, hr, hfull⟩ := GrammarGrowth.restricted_strictly_coarser
  exact hfull (h x y hr)

/-- Failure of the **strong** claim: halting an incomplete search could
prove operational identity. -/
def StallCertifiesFailure : Prop :=
  ∀ (j : ShadowWitness.activeFamily.ι) (x y : ShadowWitness.Src),
    ShadowWitness.activeFamily.Blind GrammarGrowth.restricted x y →
      ShadowWitness.activeFamily.O j x = ShadowWitness.activeFamily.O j y

theorem no_stallCertifiesFailure : ¬ StallCertifiesFailure := by
  intro h
  obtain ⟨j, x, y, hb, hne⟩ := GrammarGrowth.splitter_exists_after_stall
  exact hne (h j x y hb)

/-- Failure of the **strong** claim: splitting utility could imply
admissibility. Refuted by the decoy. -/
def UtilityImpliesAdmissibilityFailure : Prop :=
  ShadowWitness.sigSrc.Hom ShadowWitness.sigBool GrammarGrowth.decoy

theorem no_utilityImpliesAdmissibilityFailure : ¬ UtilityImpliesAdmissibilityFailure :=
  GrammarGrowth.decoy_not_hom

/-- Failure: a redundant admissible observer changes the blind remainder. -/
def RedundantGainFailure : Prop :=
  ShadowWitness.activeFamily.unresolved (insert false GrammarGrowth.restricted) ≠
    ShadowWitness.activeFamily.unresolved GrammarGrowth.restricted

theorem no_redundantGainFailure : ¬ RedundantGainFailure := by
  intro h
  exact h GrammarGrowth.redundant_zero_gain

/-- Failure: the remainder of the restricted synthesis differs from the fibres of the projection. -/
def ResidualFibreFailure : Prop :=
  ∃ x y : ShadowWitness.Src,
    ¬ (ShadowWitness.activeFamily.Blind GrammarGrowth.restricted x y ↔ ShadowWitness.sgn x = ShadowWitness.sgn y)

theorem no_residualFibreFailure : ¬ ResidualFibreFailure := by
  rintro ⟨x, y, h⟩
  exact h (GrammarGrowth.restricted_residual_is_fibre x y)

/-- **The M16.3 and M17.1 audit passes.** Five failure modes are closed: two
positive theorems and three refutations of strong claims. -/
theorem m16c_m17a_audit_passes :
    (¬ RestrictedAsFineFailure) ∧
    (¬ StallCertifiesFailure) ∧
    (¬ UtilityImpliesAdmissibilityFailure) ∧
    (¬ RedundantGainFailure) ∧
    (¬ ResidualFibreFailure) :=
  ⟨no_restrictedAsFineFailure,
   no_stallCertifiesFailure,
   no_utilityImpliesAdmissibilityFailure,
   no_redundantGainFailure,
   no_residualFibreFailure⟩

/-! ## M13d (continued) — the source filter grammar (v0.28) -/

/-- Failure: a generated logic is not closed under its own operations. -/
def GeneratedLogicClosureFailure : Prop :=
  SourceFilter.logicClosed SourceFilter.principal8 = false ∨
  SourceFilter.logicClosed SourceFilter.chain3 = false ∨
  SourceFilter.logicClosed SourceFilter.boolean4 = false ∨
  SourceFilter.logicClosed SourceFilter.nondistributive13 = false

theorem no_generatedLogicClosureFailure : ¬ GeneratedLogicClosureFailure := by
  rintro (h | h | h | h)
  · rw [SourceFilter.principal8_closed] at h; exact Bool.noConfusion h
  · rw [SourceFilter.chain3_closed] at h; exact Bool.noConfusion h
  · rw [SourceFilter.boolean4_closed] at h; exact Bool.noConfusion h
  · rw [SourceFilter.nondistributive13_closed] at h; exact Bool.noConfusion h

/-- Failure of the **strong** claim: the logic could depend on the semantic
carrier alone. Refuted by four different sizes on one and the same `B3`. -/
def LogicDependsOnCarrierOnlyFailure : Prop :=
  SourceFilter.chain3.length = SourceFilter.principal8.length

theorem no_logicDependsOnCarrierOnlyFailure : ¬ LogicDependsOnCarrierOnlyFailure := by
  intro h
  have h' : (3 : ℕ) = 8 := by
    rw [← SourceFilter.chain3_size, ← SourceFilter.principal8_size]
    exact h
  exact absurd h' (by decide)

/-- Failure of the **strong** claim: every generated logic could be Boolean.
Refuted by the thirteen-element one. -/
def AllGeneratedLogicsBooleanFailure : Prop :=
  B3.conj 149 (B3.disj 187 240) = B3.disj (B3.conj 149 187) (B3.conj 149 240)

theorem no_allGeneratedLogicsBooleanFailure : ¬ AllGeneratedLogicsBooleanFailure :=
  SourceFilter.nondistributive13_not_distributive

/-- Failure of the **strong** claim: ignoring source admissibility would not
expand the logic. -/
def AdmissibilityIrrelevantFailure : Prop :=
  B3.conditions.length ≤ SourceFilter.principal8.length

theorem no_admissibilityIrrelevantFailure : ¬ AdmissibilityIrrelevantFailure := by
  intro h
  exact absurd h (not_le.mpr SourceFilter.ignoring_admissibility_expands.2)

/-- **The M13d audit (filter grammar) passes.** Four failure modes are
closed: one positive theorem and three refutations of strong claims. -/
theorem m13d_filter_audit_passes :
    (¬ GeneratedLogicClosureFailure) ∧
    (¬ LogicDependsOnCarrierOnlyFailure) ∧
    (¬ AllGeneratedLogicsBooleanFailure) ∧
    (¬ AdmissibilityIrrelevantFailure) :=
  ⟨no_generatedLogicClosureFailure,
   no_logicDependsOnCarrierOnlyFailure,
   no_allGeneratedLogicsBooleanFailure,
   no_admissibilityIrrelevantFailure⟩

/-! ## M10 — orbit semantics, language growth, admissible continuations -/

/-- Failure: a pair of states falls into none of the three kinds. -/
def TrichotomyFailure : Prop :=
  ∃ (M : Machine.{0}) (x y : M.St),
    ¬ (Orbit.Dead M x y ∨ Orbit.Immediate M x y ∨ Orbit.Latent M x y)

theorem no_trichotomyFailure : ¬ TrichotomyFailure := by
  rintro ⟨M, x, y, h⟩
  exact h (Orbit.trichotomy x y)

/-- Failure: a latent pair has no future witness. -/
def LatentDeadFailure : Prop :=
  ∃ (M : Machine.{0}) (x y : M.St),
    Orbit.Latent M x y ∧ ∀ w : List M.Act, M.R (M.transport w x) = M.R (M.transport w y)

theorem no_latentDeadFailure : ¬ LatentDeadFailure := by
  rintro ⟨M, x, y, hl, h⟩
  exact hl.2 h

/-- Failure of the **strong** claim: a distinction of the source could
always be semantic, and immediate agreement could imply semantic
identity. -/
def RetentionFailure : Prop :=
  (∀ (N : Machine.{0}) (s t : N.St), s ≠ t → N.SemanticallyRelevant s t) ∨
  (∀ (N : Machine.{0}) (s t : N.St), N.R s = N.R t → N.Indist s t)

theorem no_retentionFailure : ¬ RetentionFailure := by
  rintro (h | h)
  · exact Orbit.source_overretains_local_underretains.1 h
  · exact Orbit.source_overretains_local_underretains.2 h

/-- Failure: incremental growth diverges from one-shot growth. -/
def IncrementalFailure : Prop :=
  ∃ (G : Growth.TwoStep.{0}) (x y : G.St), G.m₂.Indist x y ∧ ¬ G.m₀.Indist x y

theorem no_incrementalFailure : ¬ IncrementalFailure := by
  rintro ⟨G, x, y, h2, h⟩
  exact h (Growth.TwoStep.incremental_equals_fresh x y h2)

/-- Failure of the **strong** claim: a revived distinction could be detected
by the old grammar. -/
def RevivedWithoutGrowthFailure : Prop :=
  ¬ GrammarWitness.strictExp.base.Indist 0 1

theorem no_revivedWithoutGrowthFailure : ¬ RevivedWithoutGrowthFailure := by
  intro h
  exact h Growth.revived_requires_new.1

/-- Failure of the **strong** claim: public utility could be a criterion of
source admissibility. -/
def UtilityIsAdmissibilityFailure : Prop :=
  Admissible.witness.Util [false] → Admissible.witness.Adm [false]

theorem no_utilityIsAdmissibilityFailure : ¬ UtilityIsAdmissibilityFailure := by
  intro h
  exact Admissible.utility_not_admissibility.2.2.2
    (h Admissible.utility_not_admissibility.2.1)

/-- Failure: composition leads out of source admissibility. -/
def CompositionFailure : Prop :=
  ∃ (G : Admissible.Grammar) (w v : List G.Act),
    G.Adm w ∧ G.Adm v ∧ ¬ G.Adm (w ++ v)

theorem no_compositionFailure : ¬ CompositionFailure := by
  rintro ⟨G, w, v, hw, hv, h⟩
  exact h (G.adm_append w v hw hv)

/-- **The M10 audit passes.** Seven failure modes are closed: four positive
theorems and three refutations of strong claims. -/
theorem m10_audit_passes :
    (¬ TrichotomyFailure) ∧
    (¬ LatentDeadFailure) ∧
    (¬ RetentionFailure) ∧
    (¬ IncrementalFailure) ∧
    (¬ RevivedWithoutGrowthFailure) ∧
    (¬ UtilityIsAdmissibilityFailure) ∧
    (¬ CompositionFailure) :=
  ⟨no_trichotomyFailure,
   no_latentDeadFailure,
   no_retentionFailure,
   no_incrementalFailure,
   no_revivedWithoutGrowthFailure,
   no_utilityIsAdmissibilityFailure,
   no_compositionFailure⟩

/-! ## Closing downgrades #48 and #50 -/

/-- Failure: the iteration of the interval lift does not stabilize. -/
def NoStableIterationFailure : Prop :=
  ∃ Φ : Finset Bool → Finset Bool,
    ∀ n, gamma (Partial.iterI Φ (n + 1)) ≠ gamma (Partial.iterI Φ n)

theorem no_noStableIterationFailure : ¬ NoStableIterationFailure := by
  rintro ⟨Φ, h⟩
  obtain ⟨n, hn⟩ := Partial.exists_stable_iterI Φ
  exact h n hn

/-- Failure: an exact solution drops out of the partial status at some step. -/
def ExactEscapesFailure : Prop :=
  ∃ (Φ : Finset Bool → Finset Bool) (A : Finset Bool) (n : ℕ),
    ExactFixed Φ A ∧ A ∉ gamma (Partial.iterI Φ n)

theorem no_exactEscapesFailure : ¬ ExactEscapesFailure := by
  rintro ⟨Φ, A, n, hA, h⟩
  exact h (Partial.exact_mem_iterI Φ hA n)

/-- Failure of the **strong** claim: a singleton partial point could fail to
be an exact solution. -/
def SingletonNotExactFailure : Prop :=
  ∃ (Φ : Finset Bool → Finset Bool) (n : ℕ) (A : Finset Bool),
    gamma (Partial.iterI Φ (n + 1)) = gamma (Partial.iterI Φ n) ∧
    gamma (Partial.iterI Φ n) = {A} ∧ ¬ ExactFixed Φ A

theorem no_singletonNotExactFailure : ¬ SingletonNotExactFailure := by
  rintro ⟨Φ, n, A, hst, hs, h⟩
  exact h (Partial.singleton_stable_is_exact Φ hst hs)

/-- Failure: some condition is not recovered as a disjunction of principals. -/
def EnvelopeGenerationFailure : Prop :=
  SourceFilter.condition_is_join_of_principals = SourceFilter.condition_is_join_of_principals →
    B3.conditions.all (fun m => SourceFilter.joinPrincipals m == m) = false

theorem no_envelopeGenerationFailure : ¬ EnvelopeGenerationFailure := by
  intro h
  have := h rfl
  rw [SourceFilter.condition_is_join_of_principals] at this
  exact Bool.noConfusion this

/-- **Downgrades #48 and #50 are lifted.** Four failure modes are closed. -/
theorem gaps_closed_audit_passes :
    (¬ NoStableIterationFailure) ∧
    (¬ ExactEscapesFailure) ∧
    (¬ SingletonNotExactFailure) ∧
    (¬ EnvelopeGenerationFailure) :=
  ⟨no_noStableIterationFailure,
   no_exactEscapesFailure,
   no_singletonNotExactFailure,
   no_envelopeGenerationFailure⟩

end AuditBacklog

end MetaLang
