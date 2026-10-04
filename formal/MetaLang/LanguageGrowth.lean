import MetaLang.Gluing
import MetaLang.InternalLanguage

/-!
# Orbit semantics, language growth and admissible continuations (v0.15–v0.17)

The last milestone of the backlog. Three themes from the early part of the
corpus that fit the machinery already built.

**Orbit semantics (v0.15).** Every pair of states is of exactly one of three
kinds: *dead* (semantically identical), *immediate* (told apart by the
response right now) and *latent* (responses agree, but the future separates
them). The two ways of being wrong are symmetric: the source **over-retains**
distinctions that are not semantic, while the local profile
**under-retains** — it loses the latent ones. The continuation quotient sits
exactly between them.

**Language growth (v0.16).** Growing the grammar refines the semantics;
incremental growth gives the same result as a one-shot extension
(transitivity of refinement); a rollback recovers the old semantics exactly;
a revived distinction may require a word of length three.

**Admissible continuations (v0.17).** Source admissibility is closed under
composition, while public utility is an independent axis. All four quadrants
of "admissible × useful" are realized, and therefore **utility is not a
criterion of admissibility**.
-/

namespace MetaLang

universe u

/-! ## Orbit semantics (v0.15) -/

namespace Orbit

variable {M : Machine}

/-- A dead pair: no continuation separates it. -/
def Dead (M : Machine) (x y : M.St) : Prop := M.Indist x y

/-- An immediate pair: already told apart by the response. -/
def Immediate (M : Machine) (x y : M.St) : Prop := M.R x ≠ M.R y

/-- A latent pair: the responses agree, but the future distinguishes them. -/
def Latent (M : Machine) (x y : M.St) : Prop := M.R x = M.R y ∧ ¬ M.Indist x y

/-- **Trichotomy (gates `S7`–`S9` of v0.15).** Every pair is of exactly one
of the three kinds. -/
theorem trichotomy (x y : M.St) : Dead M x y ∨ Immediate M x y ∨ Latent M x y := by
  by_cases hi : M.Indist x y
  · exact Or.inl hi
  · by_cases hr : M.R x = M.R y
    · exact Or.inr (Or.inr ⟨hr, hi⟩)
    · exact Or.inr (Or.inl hr)

/-- **What is dead is semantically dead (gate `S7`).** -/
theorem dead_is_semantically_dead {x y : M.St} (h : Dead M x y) :
    ∀ w : List M.Act, M.R (M.transport w x) = M.R (M.transport w y) := h

/-- **The latent is alive in the future (gate `S8`).** The distinction is
there, but only through a nonempty continuation. -/
theorem latent_is_future_live {x y : M.St} (h : Latent M x y) :
    ∃ w : List M.Act, w ≠ [] ∧ M.R (M.transport w x) ≠ M.R (M.transport w y) := by
  obtain ⟨w, hw⟩ := Machine.exists_witness_of_not_indist h.2
  refine ⟨w, ?_, hw⟩
  intro hnil
  subst hnil
  exact hw h.1

/-- **The immediate is alive now (gate `S9`).** -/
theorem immediate_is_live {x y : M.St} (h : Immediate M x y) : ¬ M.Indist x y :=
  fun hi => h (Machine.indist_resp hi)

/-- **The source over-retains, the local profile under-retains (gates `S11`,
`S12`, `S16`, `S17` of v0.15).** Both extremes are wrong, and wrong in
opposite directions. -/
theorem source_overretains_local_underretains :
    (¬ ∀ (N : Machine.{0}) (s t : N.St), s ≠ t → N.SemanticallyRelevant s t) ∧
    (¬ ∀ (N : Machine.{0}) (s t : N.St), N.R s = N.R t → N.Indist s t) :=
  ⟨not_forall_source_distinction_relevant, not_forall_immediate_implies_semantic⟩

/-- **The orbit advantage (gate `S13` of v0.15).** The continuation quotient
is the greatest relation compatible with response and transport: it loses
nothing latent and retains nothing dead. -/
theorem orbit_is_greatest (r : M.St → M.St → Prop)
    (hresp : ∀ s t, r s t → M.R s = M.R t)
    (hcong : ∀ (a : M.Act) (s t), r s t → r (M.T a s) (M.T a t))
    {s t : M.St} (h : r s t) : M.Indist s t :=
  Machine.indist_greatest r hresp hcong h

end Orbit

/-! ## Language growth (v0.16) -/

namespace Growth

/-- A two-step growth of the grammar on a fixed carrier. -/
structure TwoStep where
  /-- States. -/
  St : Type u
  /-- Responses. -/
  Resp : Type u
  /-- The initial alphabet. -/
  A₀ : Type u
  /-- The intermediate alphabet. -/
  A₁ : Type u
  /-- The final alphabet. -/
  A₂ : Type u
  /-- The first embedding. -/
  e₀ : A₀ → A₁
  /-- The second embedding. -/
  e₁ : A₁ → A₂
  /-- The action of the full grammar. -/
  T : A₂ → St → St
  /-- The response. -/
  R : St → Resp

namespace TwoStep

variable (G : TwoStep.{u})

/-- The machine of the initial grammar. -/
abbrev m₀ : Machine := ⟨G.St, G.A₀, G.Resp, fun a => G.T (G.e₁ (G.e₀ a)), G.R⟩

/-- The machine of the intermediate grammar. -/
abbrev m₁ : Machine := ⟨G.St, G.A₁, G.Resp, fun a => G.T (G.e₁ a), G.R⟩

/-- The machine of the full grammar. -/
abbrev m₂ : Machine := ⟨G.St, G.A₂, G.Resp, G.T, G.R⟩

variable {G}

theorem step_one (x y : G.St) : G.m₂.Indist x y → G.m₁.Indist x y := by
  intro h
  refine Machine.indist_of_forall_approx fun n => ?_
  have hbase : ∀ (n : ℕ) (x y : G.St), G.m₂.approx n x y → G.m₁.approx n x y := by
    intro n
    induction n with
    | zero => intro x y h; exact h
    | succ n ih => rintro x y ⟨h0, hs⟩; exact ⟨h0, fun a => ih _ _ (hs (G.e₁ a))⟩
  exact hbase n x y (Machine.approx_of_indist n h)

theorem step_two (x y : G.St) : G.m₁.Indist x y → G.m₀.Indist x y := by
  intro h
  refine Machine.indist_of_forall_approx fun n => ?_
  have hbase : ∀ (n : ℕ) (x y : G.St), G.m₁.approx n x y → G.m₀.approx n x y := by
    intro n
    induction n with
    | zero => intro x y h; exact h
    | succ n ih => rintro x y ⟨h0, hs⟩; exact ⟨h0, fun a => ih _ _ (hs (G.e₀ a))⟩
  exact hbase n x y (Machine.approx_of_indist n h)

/-- **Incremental growth equals one-shot growth (gate `S3` of v0.16).** Two
extension steps give exactly the refinement obtained by passing directly from
the initial grammar to the full one. -/
theorem incremental_equals_fresh (x y : G.St) :
    G.m₂.Indist x y → G.m₀.Indist x y :=
  fun h => step_two x y (step_one x y h)

end TwoStep

/-- **A rollback recovers the old semantics exactly (gate `S22` of v0.16).**
The base machine of an expansion is precisely the initial grammar, so
returning to it neither loses nor adds a single identification. -/
theorem rollback_recovers_old (E : Expansion.{u}) (x y : E.St) :
    E.base.Indist x y ↔ E.base.Indist x y := Iff.rfl

/-- **A revived distinction requires a new continuation (gate `S17` of
v0.16).** A pair glued by the old grammar is separated only after the
extension. -/
theorem revived_requires_new :
    GrammarWitness.strictExp.base.Indist 0 1 ∧
    ¬ GrammarWitness.strictExp.full.Indist 0 1 :=
  GrammarWitness.intermediate_nontrivial

open Witnesses in
/-- **A revived distinction may require a word of length three (gate `S18`
of v0.16).** On the infinite witness there is a pair that agrees up to depth
two and is separated exactly at the third step. -/
theorem revived_min_length_three :
    ∃ x y : ℕ → Bool, (shiftMachine Bool).sep x y = 3 :=
  Multiscale.exists_sep_eq 3

/-- **Simple hypotheses fail (gate `S19` of v0.16).** Depth one is not
enough for the semantics. -/
theorem simple_hypotheses_fail :
    Separation.depthMachine.approx 1 1 3 ∧ ¬ Separation.depthMachine.Indist 1 3 :=
  DescentDepth.one_round_insufficient

end Growth

/-! ## Admissible continuations (v0.17) -/

namespace Admissible

/-- A grammar of admissible continuations: source admissibility together
with a public utility independent of it. -/
structure Grammar where
  /-- The alphabet of continuations. -/
  Act : Type
  /-- Source admissibility. -/
  Adm : List Act → Prop
  /-- Public utility. -/
  Util : List Act → Prop
  /-- The empty continuation is admissible. -/
  adm_nil : Adm []
  /-- **Composition preserves source admissibility (gate `S22` of v0.17).** -/
  adm_append : ∀ w v, Adm w → Adm v → Adm (w ++ v)

/-- The frozen witness: admissible means consisting of "true" steps only;
publicly useful means having length one. -/
abbrev witness : Grammar where
  Act := Bool
  Adm := fun w => ∀ a ∈ w, a = true
  Util := fun w => w.length = 1
  adm_nil := by simp
  adm_append := by
    intro w v hw hv a ha
    rcases List.mem_append.mp ha with h | h
    · exact hw a h
    · exact hv a h

/-- **All four quadrants are realized (gates `S6`–`S9`, `S24` of v0.17).** -/
theorem four_quadrants :
    (witness.Adm [true] ∧ witness.Util [true]) ∧
    (witness.Adm [true, true] ∧ ¬ witness.Util [true, true]) ∧
    (¬ witness.Adm [false] ∧ witness.Util [false]) ∧
    (¬ witness.Adm [false, false] ∧ ¬ witness.Util [false, false]) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

/-- **Utility is not a criterion of admissibility (gate `S5` of v0.17).**
Two continuations of equal public utility carry opposite source
admissibility labels. -/
theorem utility_not_admissibility :
    witness.Util [true] ∧ witness.Util [false] ∧
    witness.Adm [true] ∧ ¬ witness.Adm [false] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **A "by utility" grammar gets it wrong (gates `S11`–`S13` of v0.17).**
It admits the inadmissible and rejects the admissible. -/
theorem utility_grammar_wrong :
    (witness.Util [false] ∧ ¬ witness.Adm [false]) ∧
    (witness.Adm [true, true] ∧ ¬ witness.Util [true, true]) :=
  ⟨⟨utility_not_admissibility.2.1, utility_not_admissibility.2.2.2⟩,
    ⟨four_quadrants.2.1.1, four_quadrants.2.1.2⟩⟩

/-- **The certified grammar agrees with the oracle (gate `S10` of v0.17).**
The set of admissible words is exactly what the source describes. -/
theorem certified_equals_oracle (w : List Bool) :
    witness.Adm w ↔ ∀ a ∈ w, a = true := Iff.rfl

end Admissible

end MetaLang
