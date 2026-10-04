import MetaLang.AuditM7
import MetaLang.MeaningWitnesses

/-!
# Audit of the meaning algebra (M8)

The same discipline as in `Countermodels.lean`, `Audit.lean` and
`AuditM7.lean`: every substantive claim of phases P1–P5 gets a failure
predicate and a proof that the failure is closed. Claims the corpus
**rejects** (laws that ASC does not generate) are encoded as refuted, with
explicit countermodels.
-/

namespace MetaLang

namespace AuditM8

open Machine Witnesses

/-! ### P1: continuity and the three requirements -/

/-- Failure: an operation preserves the filtration but is not 1-Lipschitz. -/
def ContinuityFailure (M : Machine) : Prop :=
  ∃ op : M.St → M.St → M.St, ∃ _ : M.FiltrationCompat₂ op, ∃ x x' y y' : M.St,
    ¬ (M.dASC (op x y) (op x' y') ≤ max (M.dASC x x') (M.dASC y y'))

theorem no_continuityFailure (M : Machine) : ¬ ContinuityFailure M := by
  rintro ⟨op, hop, x, x', y, y', h⟩
  exact h (dASC_op_le_max hop x x' y y')

/-- Failure: filtration compatibility does not imply well-definedness on
the semantic quotient. -/
def FiltrationDescentFailure (M : Machine) : Prop :=
  ∃ op : M.St → M.St → M.St, M.FiltrationCompat₂ op ∧ ¬ M.DescentCompat₂ op

theorem no_filtrationDescentFailure (M : Machine) : ¬ FiltrationDescentFailure M := by
  rintro ⟨op, hop, h⟩
  exact h (descentCompat₂_of_filtrationCompat₂ hop)

/-- Failure of a **strong** claim: closure of an operation would imply
well-definedness on the semantic quotient. Refuted by `flatMachine`. -/
def ClosureImpliesDescentFailure : Prop :=
  ∀ (M : Machine.{0}) (op : M.St → M.St → M.St), M.DescentCompat₂ op

theorem no_closureImpliesDescentFailure : ¬ ClosureImpliesDescentFailure := by
  intro h
  exact Separation.closure_does_not_imply_descent (h Separation.flatMachine Separation.badOp)

/-- Failure of a **strong** claim: well-definedness on the semantic quotient
would imply ASC continuity. Refuted by `depthMachine`. -/
def DescentImpliesContinuityFailure : Prop :=
  ∀ (M : Machine.{0}) (op : M.St → M.St → M.St),
    M.DescentCompat₂ op → M.FiltrationCompat₂ op

theorem no_descentImpliesContinuityFailure : ¬ DescentImpliesContinuityFailure := by
  intro h
  exact Separation.descent_does_not_imply_continuity.2
    (h Separation.depthMachine Separation.coarseOp
      Separation.descent_does_not_imply_continuity.1)

/-- Failure of a **strong** claim: the book layer would impose algebraic
laws. Refuted by an explicit `BookAlgebra`. -/
def BookLayerForcesLawsFailure : Prop :=
  ∀ A : BookAlgebra (Fin 3), ∀ x y, A.oplus x y = A.oplus y x

theorem no_bookLayerForcesLawsFailure : ¬ BookLayerForcesLawsFailure := by
  intro h
  obtain ⟨A, _, _, hcomm, _⟩ := BookAlgebra.book_layer_does_not_force_laws
  exact hcomm (h A)

/-! ### P2–P3: descent of operations -/

/-- Failure: a chart map of the atlas is not a homomorphism into the global algebra. -/
def AtlasHomFailure : Prop :=
  ∃ (Q : Type) (A : AlgAtlas Q) (i : A.ι), ¬ (A.local_sig i).Hom A.global (A.pres i)

theorem no_atlasHomFailure : ¬ AtlasHomFailure := by
  rintro ⟨Q, A, i, h⟩
  exact h (A.pres_hom i)

/-- Failure: the global algebra of an atlas is not unique. -/
def AtlasUniqueFailure : Prop :=
  ∃ (Q : Type) (A : AlgAtlas Q) (B : Sig Q),
    (∀ i, (A.local_sig i).Hom B (A.pres i)) ∧ B ≠ A.global

theorem no_atlasUniqueFailure : ¬ AtlasUniqueFailure := by
  rintro ⟨Q, A, B, hB, hne⟩
  exact hne (A.global_unique B hB)

/-- Failure of a **strong** claim: totality and closure in every chart would
suffice for descent. Refuted by a pair of gauges. -/
def ClosureGlobalizesFailure : Prop :=
  ∃ μ : Bool → Bool → Bool,
    (∀ a b, μ a b = NoDescent.opAnd a b) ∧
    (∀ a b, μ (!a) (!b) = !(NoDescent.opAnd a b))

theorem no_closureGlobalizesFailure : ¬ ClosureGlobalizesFailure :=
  NoDescent.closure_without_compat_has_no_global

/-- Failure: a homomorphism fails to transport an equation of the signature. -/
def LawDescentFailure : Prop :=
  ∃ (α β : Type) (A : Sig α) (B : Sig β) (f : α → β) (V : Type) (t u : Term V),
    A.Hom B f ∧ Function.Surjective f ∧
    (∀ σ : V → α, Term.eval A σ t = Term.eval A σ u) ∧
    ∃ τ : V → β, Term.eval B τ t ≠ Term.eval B τ u

theorem no_lawDescentFailure : ¬ LawDescentFailure := by
  rintro ⟨α, β, A, B, f, V, t, u, hhom, hsurj, hlaw, τ, hne⟩
  exact hne (law_descends hhom hsurj hlaw τ)

/-- Failure: the gluing of a product atlas disagrees with a local map. -/
def ProductGlueFailure : Prop :=
  ∃ (Q : Type) (P : ProductAtlas Q) (i j : P.ι) (x y : Q),
    P.cell i j ∧ x ∈ P.chart i ∧ y ∈ P.chart j ∧ P.glue x y ≠ P.mu i j x y

theorem no_productGlueFailure : ¬ ProductGlueFailure := by
  rintro ⟨Q, P, i, j, x, y, hc, hx, hy, hne⟩
  exact hne (P.glue_eq_local i j x y hc hx hy)

/-- Failure: the gluing of a unary operation over a cover of states
disagrees with the local one. -/
def UnaryGlueFailure : Prop :=
  ∃ (Q : Type) (U : UnaryAtlas Q) (i : U.ι) (x : Q),
    x ∈ U.chart i ∧ U.glue x ≠ U.r i x

theorem no_unaryGlueFailure : ¬ UnaryGlueFailure := by
  rintro ⟨Q, U, i, x, hx, hne⟩
  exact hne (U.glue_eq_local i x hx)

/-- Failure of a **strong** claim: incompatible local maps would still glue.
Refuted by conjunction against disjunction. -/
def CorruptOverlapFailure : Prop :=
  ∃ μ : Bool → Bool → Bool, (∀ x y, μ x y = (x && y)) ∧ (∀ x y, μ x y = (x || y))

theorem no_corruptOverlapFailure : ¬ CorruptOverlapFailure :=
  ProductCounter.corrupt_overlap_no_global

/-! ### P4: witnesses -/

/-- Failure: the filtration of the shift machine is not the prefix one. -/
def PrefixFiltrationFailure : Prop :=
  ∃ (n : ℕ) (x y : ℕ → Bool),
    ¬ ((shiftMachine Bool).approx n x y ↔ ∀ i ≤ n, x i = y i)

theorem no_prefixFiltrationFailure : ¬ PrefixFiltrationFailure := by
  rintro ⟨n, x, y, h⟩
  exact h (shift_approx n x y)

/-- Failure of a **strong** claim: an ASC-continuous meaning algebra would be
forced to commute. Refuted by `D₄`. -/
def MeaningAlgebraCommutativeFailure : Prop :=
  ∀ x y : ℕ → DihedralGroup 4, GroupWitness.gplus x y = GroupWitness.gplus y x

theorem no_meaningAlgebraCommutativeFailure : ¬ MeaningAlgebraCommutativeFailure := by
  intro h
  obtain ⟨x, y, hne⟩ := GroupWitness.gplus_not_comm
  exact hne (h x y)

/-- Failure of a **strong** claim: ASC and descent would impose associativity
and an identity. Refuted by the magma. -/
def ASCForcesGroupLawsFailure : Prop :=
  ∀ (op : (ℕ → Fin 3) → (ℕ → Fin 3) → (ℕ → Fin 3)),
    (shiftMachine (Fin 3)).FiltrationCompat₂ op →
      ∀ x y z, op (op x y) z = op x (op y z)

theorem no_aSCForcesGroupLawsFailure : ¬ ASCForcesGroupLawsFailure := by
  intro h
  obtain ⟨x, y, z, hne⟩ := MagmaWitness.mop_not_assoc
  exact hne (h MagmaWitness.mop MagmaWitness.mop_filtrationCompat x y z)

/-- Failure: coordinatewise `or` is not a least upper bound, i.e. synthesis
in the infinite witness is not derived from the order. -/
def BooleanJoinFailure : Prop :=
  ∃ x y : ℕ → Bool, ¬ IsLUB {x, y} (BooleanWitness.bjoin x y)

theorem no_booleanJoinFailure : ¬ BooleanJoinFailure := by
  rintro ⟨x, y, h⟩
  exact h (BooleanWitness.bjoin_isLUB x y)

/-- Failure of a **strong** claim: the infinite witness would be discrete,
i.e. would add nothing beyond finite models. -/
def InfiniteWitnessDiscreteFailure : Prop :=
  ∃ n : ℕ, ∀ x y : ℕ → Bool, (shiftMachine Bool).approx n x y → x = y

theorem no_infiniteWitnessDiscreteFailure : ¬ InfiniteWitnessDiscreteFailure := by
  rintro ⟨n, h⟩
  obtain ⟨x, y, hne, happ⟩ := BooleanWitness.boolean_not_discrete n
  exact hne (h x y happ)

/-- Failure: the constraint order of the infinite witness is not recovered
from its continuation language. -/
def BooleanOrderRecoveryFailure : Prop :=
  ∃ x y : ℕ → Bool, ¬ (BooleanWitness.boolSys.refines x y ↔ x ≤ y)

theorem no_booleanOrderRecoveryFailure : ¬ BooleanOrderRecoveryFailure := by
  rintro ⟨x, y, h⟩
  exact h (BooleanWitness.bool_refines_iff_le x y)

/-! ### P5: completing v0.24 -/

/-- Failure: the refinement order is not recovered from the continuation language. -/
def OrderRecoveryFailure : Prop :=
  ∃ x y : Bow, ¬ ((RefinementInterface.sys Bow).refines x y ↔ x ≤ y)

theorem no_orderRecoveryFailure : ¬ OrderRecoveryFailure := by
  rintro ⟨x, y, h⟩
  exact h (RefinementInterface.refines_iff_le x y)

/-- Failure: in a Boolean algebra contrast is multivalued. -/
def BooleanContrastFailure : Prop :=
  ∃ x y : ℕ → Bool, Contrast x y ≠ {x \ y}

theorem no_booleanContrastFailure : ¬ BooleanContrastFailure := by
  rintro ⟨x, y, h⟩
  exact h (boolean_contrast_singleton x y)

/-- Failure of a **strong** claim: synthesis would be total on every
refinement order. Refuted by the bowtie. -/
def TotalSynthesisFailure : Prop :=
  ∀ (β : Type) (_ : PartialOrder β) (x y : β), ∃ z, IsSynthesis x y z

theorem no_totalSynthesisFailure : ¬ TotalSynthesisFailure := by
  intro h
  exact bow_no_synthesis (h Bow inferInstance Bow.a Bow.b)

/-! ### The summary theorem -/

/-- **The meaning-algebra audit passes.** Twenty-one failure modes are
closed: twelve positive theorems and nine refutations of strong claims, each
with an explicit countermodel. -/
theorem algebra_audit_passes :
    (∀ M : Machine, ¬ ContinuityFailure M) ∧
    (∀ M : Machine, ¬ FiltrationDescentFailure M) ∧
    (¬ ClosureImpliesDescentFailure) ∧
    (¬ DescentImpliesContinuityFailure) ∧
    (¬ BookLayerForcesLawsFailure) ∧
    (¬ AtlasHomFailure) ∧
    (¬ AtlasUniqueFailure) ∧
    (¬ ClosureGlobalizesFailure) ∧
    (¬ LawDescentFailure) ∧
    (¬ ProductGlueFailure) ∧
    (¬ UnaryGlueFailure) ∧
    (¬ CorruptOverlapFailure) ∧
    (¬ PrefixFiltrationFailure) ∧
    (¬ MeaningAlgebraCommutativeFailure) ∧
    (¬ ASCForcesGroupLawsFailure) ∧
    (¬ BooleanJoinFailure) ∧
    (¬ InfiniteWitnessDiscreteFailure) ∧
    (¬ BooleanOrderRecoveryFailure) ∧
    (¬ OrderRecoveryFailure) ∧
    (¬ BooleanContrastFailure) ∧
    (¬ TotalSynthesisFailure) :=
  ⟨no_continuityFailure,
   no_filtrationDescentFailure,
   no_closureImpliesDescentFailure,
   no_descentImpliesContinuityFailure,
   no_bookLayerForcesLawsFailure,
   no_atlasHomFailure,
   no_atlasUniqueFailure,
   no_closureGlobalizesFailure,
   no_lawDescentFailure,
   no_productGlueFailure,
   no_unaryGlueFailure,
   no_corruptOverlapFailure,
   no_prefixFiltrationFailure,
   no_meaningAlgebraCommutativeFailure,
   no_aSCForcesGroupLawsFailure,
   no_booleanJoinFailure,
   no_infiniteWitnessDiscreteFailure,
   no_booleanOrderRecoveryFailure,
   no_orderRecoveryFailure,
   no_booleanContrastFailure,
   no_totalSynthesisFailure⟩

end AuditM8

end MetaLang
