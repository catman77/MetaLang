import MetaLang.Observer
import MetaLang.Singularity
import MetaLang.ObservationDiagram
import MetaLang.OperationalEquiv
import MetaLang.SelfReference
import MetaLang.Boundary
import MetaLang.SeparationCover

/-!
# Countermodel failure modes

Following `Meaning/formal/Shaman/CountermodelSearch.lean`: for every
substantive claim, the **way it could fail** is encoded explicitly, and that
way is proved to be closed.

This matters more than a list of proved theorems: it shows what was actually
checked. The negative results of the corpus (`⇏ utility`, `⇏ channel`,
`a partial point is not truth`, underdetermination) are encoded here as
**refuted** strong claims, not as caveats.
-/

namespace MetaLang

universe u

/-! ### The internal language -/

/-- Failure: iterative refinement does not stabilize on a finite source. -/
def StabilizationFailure (M : Machine) [Fintype M.St] : Prop :=
  ¬ ∃ n : ℕ, ∀ s t : M.St, M.Indist s t ↔ M.approx n s t

theorem no_stabilizationFailure (M : Machine) [Fintype M.St] :
    ¬ StabilizationFailure M :=
  fun h => h (Machine.stabilization M)

/-- Failure: the states differ, but the difference cannot be exhibited. -/
def WitnessFailure (M : Machine) : Prop :=
  ∃ s t : M.St, ¬ M.Indist s t ∧
    ∀ w : List M.Act, M.R (M.transport w s) = M.R (M.transport w t)

theorem no_witnessFailure (M : Machine) : ¬ WitnessFailure M := by
  rintro ⟨s, t, hne, hall⟩
  exact hne hall

/-- Failure: a context creates a distinction where there was none. -/
def CongruenceFailure (M : Machine) : Prop :=
  ∃ (a : M.Act) (s t : M.St), M.Indist s t ∧ ¬ M.Indist (M.T a s) (M.T a t)

theorem no_congruenceFailure (M : Machine) : ¬ CongruenceFailure M := by
  rintro ⟨a, s, t, h, hn⟩
  exact hn (Machine.indist_congr h a)

/-! ### The observer -/

/-- Failure: renaming surface names changes the internal language. -/
def GaugeFailure (M : Machine) {St' : Type u} (e : M.St ≃ St') : Prop :=
  ∃ s t : M.St, M.Indist s t ∧ ¬ (M.relabel e).Indist (e s) (e t)

theorem no_gaugeFailure (M : Machine) {St' : Type u} (e : M.St ≃ St') :
    ¬ GaugeFailure M e := by
  rintro ⟨s, t, h, hn⟩
  exact hn ((Machine.indist_relabel_iff e s t).mpr h)

/-- Failure: the canonical projection glues semantically distinct states. -/
def LegitimacyFailure (M : Machine) : Prop := ¬ (Observer.canonical M).Legitimate

theorem no_legitimacyFailure (M : Machine) : ¬ LegitimacyFailure M :=
  fun h => h (Observer.canonical_legitimate M)

/-! ### The operational object -/

/-- Failure: the operational object does not embed subdirectly. -/
def SubdirectFailure {S : Type u} (F : ObsFamily S) : Prop :=
  ¬ Function.Injective F.etaBar

theorem no_subdirectFailure {S : Type u} (F : ObsFamily S) : ¬ SubdirectFailure F :=
  fun h => h (ObsFamily.etaBar_injective F)

/-- Failure of a **strong** claim: science would determine a unique ontic
source. Refuted by the `Q8`/`D8` pair. -/
def UnderdeterminationFailure : Prop :=
  ∀ (A B : FinGroup) (ksA ksB : List Nat),
    diagramIsos (strictDiagram A ksA) (strictDiagram B ksB) ≠ [] → Isomorphic A B

theorem no_underdeterminationFailure : ¬ UnderdeterminationFailure := fun h =>
  q8_not_isomorphic_d8 (h q8 d8 q8Kernels d8Kernels q8_d8_diagram_equivalent)

/-- Failure of a **strong** claim: the object profile would suffice for
equivalence. Refuted by the scramble countermodel. -/
def ProfileSufficiencyFailure : Prop :=
  ∀ A B : FinDiagram, A.sizes = B.sizes → diagramIsos A B ≠ []

theorem no_profileSufficiencyFailure : ¬ ProfileSufficiencyFailure := fun h =>
  h q8Diagram scrambledDiagram scramble_same_profile.symm scramble_rejected

/-! ### Boundaries -/

/-- Failure of a **strong** claim: semantic structure would determine
preferences. Refuted by two utilities with opposite orderings. -/
def UtilityFailure : Prop :=
  ∀ (M : Machine.{0}) (U₁ U₂ : M.St → ℝ),
    (∀ s t : M.St, M.Indist s t → U₁ s = U₁ t) →
    (∀ s t : M.St, M.Indist s t → U₂ s = U₂ t) →
    ∀ a b : M.St, U₁ b < U₁ a → U₂ b < U₂ a

theorem no_utilityFailure : ¬ UtilityFailure := by
  intro h
  obtain ⟨M, U₁, U₂, a, b, h₁, h₂, hlt₁, hlt₂⟩ := structure_does_not_imply_utility
  exact absurd (h M U₁ U₂ h₁ h₂ a b hlt₁) (not_lt.mpr (le_of_lt hlt₂))

/-- Failure of a **strong** claim: correspondence would imply a channel.
Refuted by the hidden-common-cause setup. -/
def ChannelFailure : Prop := ∀ C : TwoParty, C.Correspondence → C.HasChannel

theorem no_channelFailure : ¬ ChannelFailure := by
  intro h
  obtain ⟨C, hcorr, hno⟩ := correspondence_does_not_imply_channel
  exact hno (h C hcorr)

/-- Failure of a **strong** claim: a partial fixed point would always be an
exact solution. Refuted by the liar. -/
def PartialTruthFailure : Prop :=
  ∀ (Φ : Finset Bool → Finset Bool) (I : Interval Bool),
    istep Φ I = I → ∃ A : Finset Bool, ExactFixed Φ A

theorem no_partialTruthFailure : ¬ PartialTruthFailure := by
  intro h
  obtain ⟨Φ, I, hfix, hnone, _⟩ := partial_fixed_point_is_not_truth
  obtain ⟨A, hA⟩ := h Φ I hfix
  exact hnone A hA

/-! ### The solver -/

/-- Failure: on a task whose frozen family can separate everything the target separates, and with
every candidate offered to the run, the greedy run still ends with an inadmissible family. -/
def SolverFailure {Site Cand : Type} [Fintype Site] [DecidableEq Site] [Fintype Cand]
    [DecidableEq Cand] (T : Solver.Task Site Cand) (cands : List Cand)
    (_hall : ∀ d : Cand, d ∈ cands) (_hsep : T.Separable) : Prop :=
  ¬ T.Feasible (Solver.greedy T cands T.Need.card T.Need ∅)

theorem no_solverFailure {Site Cand : Type} [Fintype Site] [DecidableEq Site] [Fintype Cand]
    [DecidableEq Cand] (T : Solver.Task Site Cand) (cands : List Cand)
    (hall : ∀ d : Cand, d ∈ cands) (hsep : T.Separable) :
    ¬ SolverFailure T cands hall hsep :=
  fun h => h (T.solve_feasible cands hall hsep).1

/-- Failure: an admissible family of `k` members exists, yet the greedy run needs more than
`k · (1 + log₂ |Need|)` steps, or ends inadmissible within them. -/
def RatioFailure {Site Cand : Type} [Fintype Site] [DecidableEq Site] [Fintype Cand]
    [DecidableEq Cand] (T : Solver.Task Site Cand) (cands : List Cand) (G : Finset Cand)
    (_hG : T.Feasible G) (_hk : 1 ≤ G.card) (_hall : ∀ d : Cand, d ∈ cands) : Prop :=
  ¬ (T.Feasible (Solver.greedy T cands ((Nat.log 2 T.Need.card + 1) * G.card) T.Need ∅) ∧
      (Solver.greedy T cands ((Nat.log 2 T.Need.card + 1) * G.card) T.Need ∅).card
        ≤ (Nat.log 2 T.Need.card + 1) * G.card)

theorem no_ratioFailure {Site Cand : Type} [Fintype Site] [DecidableEq Site] [Fintype Cand]
    [DecidableEq Cand] (T : Solver.Task Site Cand) (cands : List Cand) (G : Finset Cand)
    (hG : T.Feasible G) (hk : 1 ≤ G.card) (hall : ∀ d : Cand, d ∈ cands) :
    ¬ RatioFailure T cands G hG hk hall :=
  fun h => h (T.solve_log hG hk cands hall)

/-- Failure of a **strong** claim: covering the pairs a source revealed would cover the pairs it did
not.  Refuted by an explicit three-site task, which is why the algorithmic guarantee and any claim of
transfer are kept as separate statements. -/
def TransferFailure : Prop :=
  ∀ {Site Cand : Type} [Fintype Site] [DecidableEq Site] [Fintype Cand] [DecidableEq Cand]
    (T : Solver.Task Site Cand) (O : Finset Site) (F : Finset Cand),
    T.FeasibleOn O F → T.Feasible F

theorem no_transferFailure : ¬ TransferFailure := fun h =>
  Solver.gap_feasibleOn_not_feasible.2
    (h Solver.gapTask {0, 1} Finset.univ Solver.gap_feasibleOn_not_feasible.1)

/-- Failure: a **representative** sample would still say nothing about the rest.  Closed, and
together with `no_transferFailure` this places the boundary exactly: transfer fails in general and
holds precisely under representativeness. -/
def RepresentativeFailure {Site Cand : Type} [Fintype Site] [DecidableEq Site] [Fintype Cand]
    [DecidableEq Cand] (T : Solver.Task Site Cand) (S : Finset (Site × Site)) (F : Finset Cand)
    (_hrep : T.Representative S) (_hS : S ⊆ T.Covered F) : Prop :=
  ¬ T.Feasible F

theorem no_representativeFailure {Site Cand : Type} [Fintype Site] [DecidableEq Site]
    [Fintype Cand] [DecidableEq Cand] (T : Solver.Task Site Cand) (S : Finset (Site × Site))
    (F : Finset Cand) (hrep : T.Representative S) (hS : S ⊆ T.Covered F) :
    ¬ RepresentativeFailure T S F hrep hS :=
  fun h => h (T.feasible_of_representative hrep hS)

/-! ### The language of a dissimilarity -/

/-- Failure: a scale filtration that is **not** a chain -- some larger scale glues less. -/
def ChainFailure {Site : Type} (w : Site → Site → ℕ) (t t' : ℕ) (_h : t ≤ t') : Prop :=
  ¬ (Solver.scale w t ≤ Solver.scale w t')

theorem no_chainFailure {Site : Type} (w : Site → Site → ℕ) (t t' : ℕ) (h : t ≤ t') :
    ¬ ChainFailure w t t' h :=
  fun hf => hf (Solver.scale_mono w h)

/-- Failure: the dissimilarity keeps every pair the target separates farther apart than the scale,
and the language at that scale still glues two of them.  Closed, and its converse too -- the margin
condition is not merely sufficient but exact (`scale_le_ker_iff`). -/
def MarginFailure {Site : Type} (w : Site → Site → ℕ) (f : Site → ℕ) (t : ℕ)
    (_h : ∀ x y : Site, f x ≠ f y → t < w x y) : Prop :=
  ¬ (Solver.scale w t ≤ Setoid.ker f)

theorem no_marginFailure {Site : Type} (w : Site → Site → ℕ) (f : Site → ℕ) (t : ℕ)
    (h : ∀ x y : Site, f x ≠ f y → t < w x y) :
    ¬ MarginFailure w f t h :=
  fun hf => hf ((Solver.scale_le_ker_iff w f t).mpr h)

/-! ### Encoding the target -/

/-- Failure of a **strong** claim: "coarsest recoverable encoding" would always exist.  Refuted by a
three-site witness: two recoverable encodings with no recoverable encoding coarser than both.  The
maxima are genuinely several, so a choice among them is a real branching. -/
def CoarsestEncodingFailure : Prop :=
  ∃ (R : Type) (h : Fin 3 → R), Solver.Recoverable Solver.demoObs Solver.demoAns h ∧
    (∀ i j, Solver.demoF i = Solver.demoF j → h i = h j) ∧
    (∀ i j, Solver.demoG i = Solver.demoG j → h i = h j)

theorem no_coarsestEncodingFailure : ¬ CoarsestEncodingFailure :=
  Solver.no_common_coarsening

end MetaLang
