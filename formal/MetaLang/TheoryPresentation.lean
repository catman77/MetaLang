import MetaLang.SelfReference
import MetaLang.TheorySpace
import MetaLang.ConditionLogic

/-!
# Theory presentations and typed partiality (v0.29, v0.31)

Two themes of M14 that are settled by order theory and finiteness.

**Presentations.** A theory is not a set of axioms but its deductive
closure. Hence: the closure depends only on the theory, not on the
presentation (`S3` of v0.29); extending the axioms descends through the
quotient of presentations (`S4`); one theory may have several presentations
(`S1`, `S9`).

**The signature of irreducibles.** On a finite lattice a theory is uniquely
determined by the set of meet-irreducible consequences above it (`S5`, `S6`,
`S8` of v0.29). This is not a choice of one minimal basis: the signature is
canonical.

**Typed partiality.** The outcome of admissibility is a set of branches, not
a Boolean value (`S2` of v0.31); the interval lift is **sound**: every exact
fixed point stays inside the interval (`S6`); a symmetric two-branch unknown
admits no equivariant resolution into a point (`S17`); an empty admissible
set differs from an unresolved full interval (`S24`), and an exact
bifurcation differs from an unresolved two-branch possibility (`S25`).
-/

namespace MetaLang

universe u

/-! ## Deductive closure and presentations -/

section Presentation

variable {α : Type u} [Lattice α]

/-- The closure does not distinguish a presentation from its closure. -/
theorem closure_sup_closure (c : ClosureOperator α) (a b : α) :
    c (c a ⊔ b) = c (a ⊔ b) := by
  refine le_antisymm ?_ (c.monotone (sup_le_sup_right (c.le_closure a) b))
  have h1 : c a ≤ c (a ⊔ b) := c.monotone le_sup_left
  have h2 : b ≤ c (a ⊔ b) := le_trans le_sup_right (c.le_closure _)
  calc c (c a ⊔ b) ≤ c (c (a ⊔ b)) := c.monotone (sup_le h1 h2)
    _ = c (a ⊔ b) := c.idempotent _

/-- **Extending the axioms descends through the quotient of presentations
(gate `S4` of v0.29).** If two presentations define the same theory, then
their extensions by one and the same set define the same theory too. -/
theorem extension_descends (c : ClosureOperator α) {a a' : α}
    (h : c a = c a') (b : α) : c (a ⊔ b) = c (a' ⊔ b) := by
  rw [← closure_sup_closure c a b, h, closure_sup_closure]

end Presentation

/-- A closure on the chain `Fin 3`: everything nonempty collapses to the top. -/
def chainClosure : ClosureOperator (Fin 3) where
  toFun := fun x => if x = 0 then 0 else 2
  monotone' := by decide
  le_closure' := by decide
  idempotent' := by decide

/-- **One theory may have several presentations (gates `S1`, `S9` of
v0.29).** Different sets of axioms give the same deductive closure. -/
theorem multiple_presentations :
    ∃ a b : Fin 3, a ≠ b ∧ chainClosure a = chainClosure b :=
  ⟨1, 2, by decide, by decide⟩

/-! ## The signature of meet-irreducibles -/

section Signature

variable {α : Type u} [Lattice α] [Finite α]

/-- **A separating irreducible exists.** If `a` is not below `b`, then there
is a meet-irreducible element above `b` that does not dominate `a`. -/
theorem exists_infIrred_separating {a b : α} (hab : ¬ a ≤ b) :
    ∃ m : α, InfIrred m ∧ b ≤ m ∧ ¬ a ≤ m := by
  obtain ⟨m, hm, hmax⟩ :=
    Set.Finite.exists_maximal (s := {m : α | b ≤ m ∧ ¬ a ≤ m})
      (Set.toFinite _) ⟨b, le_refl b, hab⟩
  refine ⟨m, ⟨?_, ?_⟩, hm.1, hm.2⟩
  · intro htop
    exact hm.2 (le_trans le_sup_right (htop (le_sup_left : m ≤ m ⊔ a)))
  · intro p q hpq
    by_contra hne
    push_neg at hne
    have hmp : m ≤ p := hpq ▸ inf_le_left
    have hmq : m ≤ q := hpq ▸ inf_le_right
    have hap : a ≤ p := by
      by_contra hap
      exact hne.1 (le_antisymm (hmax ⟨le_trans hm.1 hmp, hap⟩ hmp) hmp)
    have haq : a ≤ q := by
      by_contra haq
      exact hne.2 (le_antisymm (hmax ⟨le_trans hm.1 hmq, haq⟩ hmq) hmq)
    exact hm.2 (hpq ▸ le_inf hap haq)

/-- The signature of a theory: the irreducible consequences above it. -/
def irredSignature (a : α) : Set α := {m | InfIrred m ∧ a ≤ m}

/-- **The signature of irreducibles determines the theory uniquely (gates
`S5`, `S6`, `S8` of v0.29).** It is a canonical object, not a choice of one
minimal basis of axioms. -/
theorem eq_of_irredSignature_eq {a b : α}
    (h : irredSignature a = irredSignature b) : a = b := by
  refine le_antisymm ?_ ?_
  · by_contra hab
    obtain ⟨m, hm, hbm, ham⟩ := exists_infIrred_separating hab
    have : m ∈ irredSignature b := ⟨hm, hbm⟩
    rw [← h] at this
    exact ham this.2
  · by_contra hba
    obtain ⟨m, hm, ham, hbm⟩ := exists_infIrred_separating hba
    have : m ∈ irredSignature a := ⟨hm, ham⟩
    rw [h] at this
    exact hbm this.2

end Signature

/-! ## Typed partiality -/

namespace Partial

/-- **The interval lift is sound (gate `S6` of v0.31).** An exact fixed
point lying in the interval stays there after a step: no solution is
lost. -/
theorem exact_mem_gamma_istep (Φ : Finset Bool → Finset Bool) (I : Interval Bool)
    {A : Finset Bool} (hA : ExactFixed Φ A) (hmem : A ∈ gamma I) :
    A ∈ gamma (istep Φ I) := by
  simp only [gamma, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
  constructor
  · intro b hb
    simp only [istep, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have := hb A (by
      simp only [gamma, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmem)
    rwa [hA] at this
  · intro b hb
    simp only [istep, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨A, ?_, ?_⟩
    · simp only [gamma, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmem
    · rwa [hA]

/-- **The partial status is a genuine interval `L ⊆ U` (gate `S3` of
v0.31).** The status computed by a step is always coherent: what is
definitely admissible lies inside what is possibly admissible. -/
theorem istep_lo_subset_hi (Φ : Finset Bool → Finset Bool) (I : Interval Bool)
    (hne : (gamma I).Nonempty) : (istep Φ I).lo ⊆ (istep Φ I).hi := by
  intro b hb
  simp only [istep, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
  obtain ⟨A, hA⟩ := hne
  exact ⟨A, hA, hb A hA⟩

/-- **The outcome is typed as a set of branches, not a Boolean value (gate
`S2` of v0.31).** One and the same self-reference signature yields zero, one
and four exact solutions. -/
theorem outcome_is_branch_set :
    (∀ A : Finset Bool, ¬ ExactFixed liar A) ∧
    (∃ A : Finset Bool, ExactFixed constPhi A) ∧
    (∀ A : Finset Bool, ExactFixed idPhi A) :=
  ⟨liar_no_exact_fixed, ⟨{true}, by decide⟩, idPhi_all_fixed⟩

/-- Swapping the branches. -/
def swapI (I : Interval Bool) : Interval Bool :=
  ⟨I.lo.image Bool.not, I.hi.image Bool.not⟩

theorem swap_full : swapI fullInterval = fullInterval := by
  ext1
  · show (∅ : Finset Bool).image Bool.not = ∅
    decide
  · show (Finset.univ : Finset Bool).image Bool.not = Finset.univ
    decide

/-- **No equivariant resolution into a point exists (gate `S17` of
v0.31).** A symmetric two-branch unknown admits no choice of a single branch
compatible with the symmetry. -/
theorem no_equivariant_tiebreak (f : Interval Bool → Finset Bool)
    (hequiv : ∀ I, f (swapI I) = (f I).image Bool.not)
    (b : Bool) (hsing : f fullInterval = {b}) : False := by
  have h := hequiv fullInterval
  rw [swap_full, hsing] at h
  have : ({b} : Finset Bool) = {!b} := by
    rw [h]
    simp
  have hb : b = !b := by
    have := Finset.singleton_injective this
    exact this
  exact absurd hb (by cases b <;> decide)

/-- The empty admissible set. -/
def emptyInterval : Interval Bool := ⟨∅, ∅⟩

/-- **An empty admissible set differs from an unresolved full interval (gate
`S24` of v0.31).** -/
theorem empty_ne_unknown :
    (gamma emptyInterval).card = 1 ∧ (gamma fullInterval).card = 4 := by
  refine ⟨by decide, liar_gamma_full⟩

/-- A transformer with exactly two exact solutions: the endpoints are fixed,
the middle is flipped. -/
def bifurcated : Finset Bool → Finset Bool := fun A =>
  if A = ∅ then ∅ else if A = Finset.univ then Finset.univ else Aᶜ

theorem bifurcated_two_solutions :
    ExactFixed bifurcated ∅ ∧ ExactFixed bifurcated Finset.univ ∧
    ¬ ExactFixed bifurcated {true} ∧ ¬ ExactFixed bifurcated {false} := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **An exact bifurcation is indistinguishable from unresolvedness at the
partial layer (gate `S25` of v0.31).** A transformer with two exact solutions
has the same fully unknown status as the liar, which has none. -/
theorem bifurcated_interval_fixed : istep bifurcated fullInterval = fullInterval := by
  ext1
  · show (Finset.univ.filter (fun b => ∀ A ∈ gamma fullInterval, b ∈ bifurcated A)) = ∅
    decide
  · show (Finset.univ.filter (fun b => ∃ A ∈ gamma fullInterval, b ∈ bifurcated A))
        = Finset.univ
    decide

theorem bifurcation_indistinguishable_from_unknown :
    istep bifurcated fullInterval = fullInterval ∧
    istep liar fullInterval = fullInterval :=
  ⟨bifurcated_interval_fixed, liar_interval_fixed⟩

/-! ### The least partial fixed point as a limit -/

section Limit

variable {B : Type} [Fintype B] [DecidableEq B]

/-- Total unknownness on an arbitrary set of branches. -/
def topInterval (B : Type) [Fintype B] [DecidableEq B] : Interval B :=
  ⟨∅, Finset.univ⟩

@[simp] theorem gamma_topInterval : gamma (topInterval B) = Finset.univ := by
  ext A
  simp [gamma, topInterval]

/-- Concretization is monotone under narrowing of the interval. -/
theorem gamma_mono {I J : Interval B} (hlo : J.lo ⊆ I.lo) (hhi : I.hi ⊆ J.hi) :
    gamma I ⊆ gamma J := by
  intro A hA
  simp only [gamma, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
  exact ⟨fun b hb => hA.1 (hlo hb), fun b hb => hhi (hA.2 hb)⟩

/-- Iterating the interval lift from total unknownness. -/
def iterI (Φ : Finset B → Finset B) : ℕ → Interval B
  | 0 => topInterval B
  | n + 1 => istep Φ (iterI Φ n)

/-- **Iteration only refines the status.** -/
theorem gamma_iterI_antitone (Φ : Finset B → Finset B) :
    ∀ n, gamma (iterI Φ (n + 1)) ⊆ gamma (iterI Φ n) := by
  intro n
  induction n with
  | zero =>
      rw [iterI, gamma_topInterval]
      exact fun A _ => Finset.mem_univ A
  | succ n ih =>
      have hmono := istep_mono Φ ih
      exact gamma_mono hmono.1 hmono.2

/-- **A canonically least partial fixed point exists (gate `S5` of
v0.31).** The iteration from total unknownness stabilizes on a finite set of
branches. -/
theorem exists_stable_iterI (Φ : Finset B → Finset B) :
    ∃ n, gamma (iterI Φ (n + 1)) = gamma (iterI Φ n) := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ n, (gamma (iterI Φ (n + 1))).card < (gamma (iterI Φ n)).card := by
    intro n
    exact Finset.card_lt_card
      (lt_of_le_of_ne (gamma_iterI_antitone Φ n) (hcon n))
  have hbound : ∀ n, (gamma (iterI Φ n)).card + n ≤ (gamma (iterI Φ 0)).card := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := hlt n; omega
  have := hbound ((gamma (iterI Φ 0)).card + 1)
  omega

/-- **Every exact solution is contained in the partial status at every step
(gate `S6` of v0.31).** -/
theorem exact_mem_iterI (Φ : Finset B → Finset B) {A : Finset B}
    (hA : ExactFixed Φ A) : ∀ n, A ∈ gamma (iterI Φ n) := by
  intro n
  induction n with
  | zero => rw [iterI, gamma_topInterval]; exact Finset.mem_univ A
  | succ n ih =>
      refine (?_ : A ∈ gamma (istep Φ (iterI Φ n)))
      simp only [gamma, Finset.mem_filter, Finset.mem_univ, true_and] at ih ⊢
      constructor
      · intro b hb
        simp only [istep, Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have := hb A (by
          simp only [gamma, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ih)
        rwa [hA] at this
      · intro b hb
        simp only [istep, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨A, ?_, ?_⟩
        · simp only [gamma, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ih
        · rwa [hA]

/-- Filtering by membership in a fixed set gives back that set. -/
theorem filter_mem_eq (S : Finset B) :
    (Finset.univ.filter fun b => b ∈ S) = S := by
  ext b
  simp

/-- A step from an interval with a single concretization. -/
theorem istep_of_singleton (Φ : Finset B → Finset B) (I : Interval B)
    {A : Finset B} (h : gamma I = {A}) : istep Φ I = ⟨Φ A, Φ A⟩ := by
  have hmem : ∀ C : Finset B, C ∈ gamma I ↔ C = A := by
    intro C; rw [h]; simp
  ext1
  · show (Finset.univ.filter fun b => ∀ C ∈ gamma I, b ∈ Φ C) = Φ A
    rw [← filter_mem_eq (Φ A)]
    apply Finset.filter_congr
    intro b _
    constructor
    · intro hb; exact hb A ((hmem A).mpr rfl)
    · intro hb C hC; rw [(hmem C).mp hC]; exact hb
  · show (Finset.univ.filter fun b => ∃ C ∈ gamma I, b ∈ Φ C) = Φ A
    rw [← filter_mem_eq (Φ A)]
    apply Finset.filter_congr
    intro b _
    constructor
    · rintro ⟨C, hC, hb⟩; rwa [(hmem C).mp hC] at hb
    · intro hb; exact ⟨A, (hmem A).mpr rfl, hb⟩

theorem gamma_diag (S : Finset B) : gamma (⟨S, S⟩ : Interval B) = {S} := by
  ext C
  simp only [gamma, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => Finset.Subset.antisymm h.2 h.1, fun h => by rw [h]; exact ⟨le_refl S, le_refl S⟩⟩

/-- **A singleton partial fixed point is always exact (gate `S7` of
v0.31).** If the stabilized status contains exactly one branch configuration,
that configuration is an exact solution. -/
theorem singleton_stable_is_exact (Φ : Finset B → Finset B) {n : ℕ} {A : Finset B}
    (hstable : gamma (iterI Φ (n + 1)) = gamma (iterI Φ n))
    (hsing : gamma (iterI Φ n) = {A}) : ExactFixed Φ A := by
  have hstep : istep Φ (iterI Φ n) = ⟨Φ A, Φ A⟩ := istep_of_singleton Φ _ hsing
  have : gamma (istep Φ (iterI Φ n)) = {A} := by rw [← hsing, ← hstable]; rfl
  rw [hstep, gamma_diag] at this
  exact Finset.singleton_injective this

/-- **A partial point of the source is exact within one refinement step
(gate `S15` of v0.31).** For the constant transformer the iteration from
total unknownness collapses to a singleton already at the first step. -/
theorem constPhi_exact_in_one_step :
    gamma (iterI constPhi 1) = {({true} : Finset Bool)} := by decide

theorem constPhi_stable : gamma (iterI constPhi 2) = gamma (iterI constPhi 1) := by
  decide

/-- **Partial completion preserves every exact solution but may be
incomplete (gate `S27` of v0.31).** On the left, the general preservation
theorem; on the right, the liar, whose completion stays the full interval of
four configurations and singles out nothing. -/
theorem completion_preserves_but_incomplete :
    (∀ (Φ : Finset Bool → Finset Bool) (A : Finset Bool),
      ExactFixed Φ A → ∀ n, A ∈ gamma (iterI Φ n)) ∧
    (gamma (iterI liar 1)).card = 4 := by
  refine ⟨fun Φ A hA n => exact_mem_iterI Φ hA n, by decide⟩

end Limit

end Partial

end MetaLang
