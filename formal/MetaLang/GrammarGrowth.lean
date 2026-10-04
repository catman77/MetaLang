import MetaLang.OperationalAlgebra

/-!
# Observer synthesis and grammar growth (v0.35, v0.36)

Two milestones on a single witness — the sign projection `S₃ → Bool`,
extended by the identity observer.

**Restricted grammar versus full (v0.35).** Restricting to one observer
yields a nontrivial terminal blind relation, and that relation is exactly the
fibres of the projection: the "remainder" of the restricted synthesis is the
nuisance quotient. The full grammar is jointly faithful, i.e. its operational
equivalence coincides with identity of the source. Hence: the halting of a
restricted search does **not** prove operational identity — a splitter
exists, it simply is not in the current grammar.

**Admissibility versus utility (v0.36).** A candidate observer must be a
homomorphism of the source. There is a map that splits a pair invisible to
the current grammar — and is nevertheless rejected, because it is not a
homomorphism. Conversely, a redundant admissible observer is accepted with
zero gain. Splitting utility and admissibility are different things.
-/

namespace MetaLang

namespace GrammarGrowth

open ShadowWitness DihedralGroup

/-! ## Restricted and full grammar -/

/-- The restricted grammar: the sign observer only. -/
def restricted : Set activeFamily.ι := {false}

theorem restricted_blind_iff (x y : Src) :
    activeFamily.Blind restricted x y ↔ sgn x = sgn y := by
  constructor
  · intro h
    exact h false rfl
  · intro h i hi
    have : i = false := hi
    subst this
    exact h

/-- **The terminal blind relation of the restricted grammar is nontrivial
(gates `S5`, `S15` of v0.35).** -/
theorem restricted_blind_nontrivial :
    ∃ x y : Src, x ≠ y ∧ activeFamily.Blind restricted x y := by
  refine ⟨r 0, r 1, by decide, (restricted_blind_iff _ _).mpr rfl⟩

/-- **The remainder of the restricted synthesis is exactly the nuisance
quotient (gates `S16`, `S17` of v0.35).** The blind relation of the grammar
coincides with the fibres of its only projection. -/
theorem restricted_residual_is_fibre (x y : Src) :
    activeFamily.Blind restricted x y ↔ sgn x = sgn y :=
  restricted_blind_iff x y

/-- **The full grammar yields identity of the source (gate `S13` of v0.35).** -/
theorem full_blind_trivial (x y : Src) :
    activeFamily.Blind (Set.univ : Set activeFamily.ι) x y → x = y := by
  intro h
  exact activeFamily_faithful x y (fun i => h i (Set.mem_univ i))

/-- **The restricted grammar is strictly coarser than the full one (gate `S4` of v0.35).** -/
theorem restricted_strictly_coarser :
    ∃ x y : Src, activeFamily.Blind restricted x y ∧
      ¬ activeFamily.Blind (Set.univ : Set activeFamily.ι) x y := by
  refine ⟨r 0, r 1, (restricted_blind_iff _ _).mpr rfl, ?_⟩
  intro h
  exact absurd (full_blind_trivial _ _ h) (by decide)

/-- **Halting an incomplete search does not prove operational identity
(gates `S24`, `S25` of v0.35).** A splitter exists — it just is not in the
current grammar. -/
theorem splitter_exists_after_stall :
    ∃ (j : activeFamily.ι) (x y : Src),
      activeFamily.Blind restricted x y ∧ activeFamily.O j x ≠ activeFamily.O j y := by
  refine ⟨true, r 0, r 1, (restricted_blind_iff _ _).mpr rfl, ?_⟩
  show (r 0 : Src) ≠ r 1
  decide

/-- **Growing the grammar refines the quotient down to identity of the
source (gate `S26` of v0.35).** -/
theorem expansion_reaches_identity : activeFamily.Faithful := activeFamily_faithful

/-! ## Admissibility is not splitting utility -/

/-- The decoy: a map with large splitting power that is not a homomorphism. -/
def decoy : Src → Bool
  | .r i => i = 0
  | .sr i => i = 0

/-- The decoy splits a pair invisible to the sign grammar. -/
theorem decoy_splits : decoy (r 0) ≠ decoy (r 1) := by decide

/-- **The decoy is rejected despite maximal gain (gates `S6`, `S7` of
v0.36).** It is not a homomorphism of the source. -/
theorem decoy_not_hom : ¬ sigSrc.Hom sigBool decoy := by
  intro h
  have hd := h.1 (r 1) (r 2)
  revert hd
  decide

/-- **A redundant admissible observer is accepted with zero gain (gates
`S10`, `S11` of v0.36).** -/
theorem redundant_zero_gain :
    activeFamily.unresolved (insert false restricted) =
      activeFamily.unresolved restricted := by
  refine AlgObsFamily.zero_gain_of_equivalent ?_
  intro x y hb
  exact (restricted_blind_iff x y).mp hb

/-- **Admissibility is not identified with splitting utility (gate `S12` of
v0.36).** On the left, large splitting without admissibility; on the right,
admissibility without splitting. -/
theorem admissibility_ne_utility :
    (decoy (r 0) ≠ decoy (r 1) ∧ ¬ sigSrc.Hom sigBool decoy) ∧
    (sigSrc.Hom sigBool sgn ∧
      activeFamily.unresolved (insert false restricted) =
        activeFamily.unresolved restricted) :=
  ⟨⟨decoy_splits, decoy_not_hom⟩, ⟨sgn_hom, redundant_zero_gain⟩⟩

/-- **The sign projection is an admissible primitive (gate `S5` of v0.36).** -/
theorem sgn_admissible : sigSrc.Hom sigBool sgn := sgn_hom

/-- **The absence of a splitter in the current grammar does not license the
quotient when admissible growth exists (gate `S37` of v0.36).** -/
theorem no_splitter_does_not_license :
    (∀ x y : Src, activeFamily.Blind restricted x y → sgn x = sgn y) ∧
    (∃ j : activeFamily.ι, ∃ x y : Src,
      activeFamily.Blind restricted x y ∧ activeFamily.O j x ≠ activeFamily.O j y) :=
  ⟨fun x y h => (restricted_blind_iff x y).mp h, splitter_exists_after_stall⟩

/-! ## The three outcomes of the active-science cycle -/

/-- **The active-science cycle: refine the object or refactor it (gate `S36`
of v0.35).** Either the accessible class contains a splitter of the current
blind remainder, or the remainder is empty and the quotient is certified.
With a jointly faithful class there is no third case. -/
theorem refine_or_refactor {S : Type} (F : AlgObsFamily S) (hf : F.Faithful)
    (I : Set F.ι) :
    (∃ (j : F.ι) (x y : S), x ≠ y ∧ F.Blind I x y ∧ F.O j x ≠ F.O j y) ∨
      F.unresolved I = ∅ := by
  by_cases h : (F.unresolved I).Nonempty
  · exact Or.inl (AlgObsFamily.exists_refining_observer hf h)
  · exact Or.inr (Set.not_nonempty_iff_eq_empty.mp h)

/-- **Three distinct outcomes (gate `S35` of v0.35).** A splitter is found;
the search is incomplete — a splitter exists but outside the current grammar;
a certificate that no splitting remains. The first two are told apart
precisely by the grammar. -/
theorem three_outcomes :
    (∃ (j : activeFamily.ι) (x y : Src),
      activeFamily.Blind restricted x y ∧ activeFamily.O j x ≠ activeFamily.O j y) ∧
    (∀ x y : Src, activeFamily.Blind restricted x y → sgn x = sgn y) ∧
    (∀ x y : Src, activeFamily.Blind (Set.univ : Set activeFamily.ι) x y → x = y) :=
  ⟨splitter_exists_after_stall,
    fun x y h => (restricted_blind_iff x y).mp h,
    full_blind_trivial⟩

/-- **The oracle identity is a homomorphism (gate `S8` of v0.36).** Its
rejection is not structural: it is declared inaccessible, not inadmissible. -/
theorem identity_is_hom : sigSrc.Hom sigSrc (id : Src → Src) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

end GrammarGrowth

end MetaLang
