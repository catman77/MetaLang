import MetaLang.Congruence

/-!
# The internal language: the relevance criterion and its countermodels

This file records the **corrected** criterion of semantic relevance from
v0.15 together with the two negative results that led to it. Both negative
results are formalized as finite countermodels, not as caveats in prose:

* `source distinction ≠ semantic distinction` — the v0.14 mistake: source
  structure may not be retained merely because it exists;
* `immediate effect ≠ semantic effect` — v0.13: a distinction can be latent
  and show up only through a composite word of continuations.
-/

namespace MetaLang

namespace Machine

variable {M : Machine}

/-! ### The v0.15 criterion -/

/-- A distinction between `s` and `t` is semantically relevant when there is
a reachable admissible future in which it produces an observable effect.

`Meaning(d | q) = reachable counterfactual effect of d over admissible futures.` -/
def SemanticallyRelevant (M : Machine) (s t : M.St) : Prop := ¬ M.Indist s t

/-- Relevance is **equivalent** to the existence of a reachable witness.
That is the operational content of the criterion: not "the difference exists
in the source" but "the difference is reachable by observation". -/
theorem semanticallyRelevant_iff_reachable (s t : M.St) :
    M.SemanticallyRelevant s t ↔
      ∃ w : List M.Act, M.R (M.transport w s) ≠ M.R (M.transport w t) := by
  constructor
  · exact exists_witness_of_not_indist
  · rintro ⟨w, hw⟩ hind
    exact hw (hind w)

end Machine

/-! ### Countermodel 1: source distinction ≠ semantic distinction

The v0.14 mistake. The source separates two states, yet no admissible future
reaches that difference. Keeping such a difference in the quotient means
over-retaining hidden structure. -/

/-- Two source states that no future distinguishes. -/
abbrev blindMachine : Machine where
  St := Fin 2
  Act := Unit
  Resp := Unit
  T := fun _ s => s
  R := fun _ => ()

theorem blind_transport (w : List Unit) (s : Fin 2) :
    blindMachine.transport w s = s := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact ih s

/-- **`source distinction ≠ semantic distinction`.** The states differ in
the source yet are semantically identical: no admissible future separates
them. -/
theorem sourceDistinctionNotSemantic :
    ∃ s t : blindMachine.St, s ≠ t ∧ blindMachine.Indist s t := by
  refine ⟨0, 1, by decide, ?_⟩
  intro w
  rfl

/-- The negative form: the existence of a difference in the source does
**not** imply its semantic relevance. -/
theorem not_forall_source_distinction_relevant :
    ¬ ∀ (N : Machine.{0}) (s t : N.St), s ≠ t → N.SemanticallyRelevant s t := by
  intro hall
  obtain ⟨s, t, hne, hind⟩ := sourceDistinctionNotSemantic
  exact hall blindMachine s t hne hind

/-! ### Countermodel 2: immediate effect ≠ semantic effect

The v0.13 lesson. The distinction is latent: the immediate responses agree,
one step of context does not separate them either, and only a composite word
of length two exhibits the difference. One-step semantics is not enough. -/

/-- A transition with a latent distinction: from `0` two steps reach the
observable state `4`, from `1` they do not. -/
def latentT : Unit → Fin 5 → Fin 5 := fun _ s =>
  if s = 0 then 2 else if s = 1 then 3 else if s = 2 then 4 else if s = 3 then 3 else 4

/-- Only the state `4` is observable. -/
def latentR : Fin 5 → Bool := fun s => s == 4

/-- A machine with a latent distinction. -/
abbrev latentMachine : Machine where
  St := Fin 5
  Act := Unit
  Resp := Bool
  T := latentT
  R := latentR

/-- The immediate responses agree. -/
theorem latent_immediate_eq : latentMachine.R 0 = latentMachine.R 1 := by decide

/-- One step of context is not enough either: the distinction stays hidden. -/
theorem latent_approx_one : latentMachine.approx 1 0 1 := by
  refine ⟨by decide, ?_⟩
  rintro ⟨⟩
  rfl

/-- **`immediate effect ≠ semantic effect`.** The distinction exists but is
exhibited only by a composite continuation word of length two. -/
theorem immediateEffectNotSemantic :
    latentMachine.R 0 = latentMachine.R 1 ∧
      latentMachine.approx 1 0 1 ∧
      latentMachine.SemanticallyRelevant 0 1 := by
  refine ⟨latent_immediate_eq, latent_approx_one, ?_⟩
  intro hind
  have hw := hind [(), ()]
  exact absurd hw (by decide)

/-- The witness of difference has length two: one-step semantics falls short. -/
theorem latent_witness_length_two :
    ∃ w : List latentMachine.Act,
      w.length = 2 ∧
      latentMachine.R (latentMachine.transport w 0)
        ≠ latentMachine.R (latentMachine.transport w 1) := by
  exact ⟨[(), ()], rfl, by decide⟩

/-- In general: agreement of immediate responses does **not** imply
semantic identity. -/
theorem not_forall_immediate_implies_semantic :
    ¬ ∀ (N : Machine.{0}) (s t : N.St), N.R s = N.R t → N.Indist s t := by
  intro hall
  obtain ⟨himm, _, hrel⟩ := immediateEffectNotSemantic
  exact hrel (hall latentMachine 0 1 himm)

end MetaLang
