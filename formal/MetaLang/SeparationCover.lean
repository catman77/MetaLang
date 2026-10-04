import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Finset.Max
import MetaLang.AlgebraicDescent

/-!
# Separation as a covering problem

A solver is handed a finite source, a target revealed on it, and a **frozen** family of candidate
distinctions.  It must choose a subfamily whose common refinement does not glue two sites the target
separates — that is exactly the corpus's requirement that the target factor through the quotient.

Stated that way the choice is a **covering problem**: each candidate covers the pairs it separates,
and a subfamily is admissible exactly when it covers every pair the target separates.  This file
sets up that correspondence and proves the bridge between the two readings; the greedy algorithm and
its guarantees are built on it.

Nothing here assumes anything about *how* the candidates arise.  Which family is offered is the
frozen hypothesis class of the corpus's P5, and no claim below says a covering of the revealed pairs
transfers to pairs that were never revealed — that is a separate, inductive statement.
-/

namespace MetaLang.Solver

universe u v

variable {Site : Type u} {Cand : Type v}

/-- A task: a family of candidate distinctions and the target they must separate.

A distinction is read through its kernel, so its values carry no meaning beyond equality, and the
target likewise. -/
structure Task (Site : Type u) (Cand : Type v) where
  /-- The value a candidate distinction takes at a site. -/
  dist : Cand → Site → ℕ
  /-- The target revealed at a site. -/
  target : Site → ℕ

namespace Task

variable (T : Task Site Cand)

/-- The relation "every chosen candidate agrees here": the common refinement of the chosen
kernels, written directly rather than as an infimum so that no lattice plumbing is needed. -/
def agree (F : Finset Cand) : Setoid Site where
  r x y := ∀ d ∈ F, T.dist d x = T.dist d y
  iseqv :=
    { refl := fun _ _ _ => rfl
      symm := fun h d hd => (h d hd).symm
      trans := fun h₁ h₂ d hd => (h₁ d hd).trans (h₂ d hd) }

@[simp] theorem agree_apply (F : Finset Cand) (x y : Site) :
    (T.agree F).r x y ↔ ∀ d ∈ F, T.dist d x = T.dist d y := Iff.rfl

variable [Fintype Site] [DecidableEq Site] [Fintype Cand] [DecidableEq Cand]

/-- The pairs the target separates: exactly what a solution must not glue. -/
def Need : Finset (Site × Site) :=
  Finset.univ.filter fun p => T.target p.1 ≠ T.target p.2

/-- The pairs one candidate separates, among those that must be separated. -/
def Cov (d : Cand) : Finset (Site × Site) :=
  T.Need.filter fun p => T.dist d p.1 ≠ T.dist d p.2

/-- What a chosen subfamily separates. -/
def Covered (F : Finset Cand) : Finset (Site × Site) :=
  F.biUnion T.Cov

/-- A subfamily is admissible when it separates everything the target separates. -/
def Feasible (F : Finset Cand) : Prop := T.Need ⊆ T.Covered F

omit [DecidableEq Site] [Fintype Cand] [DecidableEq Cand] in
@[simp] theorem mem_Need {p : Site × Site} :
    p ∈ T.Need ↔ T.target p.1 ≠ T.target p.2 := by
  simp [Need, Finset.mem_filter]

omit [DecidableEq Site] [Fintype Cand] [DecidableEq Cand] in
@[simp] theorem mem_Cov {d : Cand} {p : Site × Site} :
    p ∈ T.Cov d ↔ (T.target p.1 ≠ T.target p.2 ∧ T.dist d p.1 ≠ T.dist d p.2) := by
  simp [Cov, Need, Finset.mem_filter]

omit [Fintype Cand] [DecidableEq Cand] in
@[simp] theorem mem_Covered {F : Finset Cand} {p : Site × Site} :
    p ∈ T.Covered F ↔ ∃ d ∈ F, p ∈ T.Cov d := by
  simp [Covered, Finset.mem_biUnion]

omit [Fintype Cand] [DecidableEq Cand] in
/-- **The bridge.** Covering the separated pairs and factoring the target through the quotient are
the same statement.  The left side is the combinatorial problem a solver can attack; the right side
is the corpus's condition that the observer not glue what the continuation separates. -/
theorem feasible_iff_le_ker (F : Finset Cand) :
    T.Feasible F ↔ T.agree F ≤ Setoid.ker T.target := by
  constructor
  · intro hF x y hxy
    by_contra hne
    have hp : (x, y) ∈ T.Need := by simpa [Need] using hne
    obtain ⟨d, hdF, hd⟩ := T.mem_Covered.mp (hF hp)
    exact (T.mem_Cov.mp hd).2 (hxy d hdF)
  · intro hle p hp
    by_contra hcov
    have : ∀ d ∈ F, T.dist d p.1 = T.dist d p.2 := by
      intro d hd
      by_contra hne
      exact hcov (T.mem_Covered.mpr ⟨d, hd, T.mem_Cov.mpr ⟨(T.mem_Need.mp hp), hne⟩⟩)
    exact (T.mem_Need.mp hp) (hle this)

/-- A task is **separable** when the frozen family can separate everything the target separates.
Nothing can be promised about a task that is not; the solver must fail closed there. -/
def Separable : Prop := ∀ p ∈ T.Need, ∃ d : Cand, p ∈ T.Cov d

omit [DecidableEq Cand] in
theorem separable_iff_feasible_univ : T.Separable ↔ T.Feasible (Finset.univ : Finset Cand) := by
  constructor
  · intro h p hp
    obtain ⟨d, hd⟩ := h p hp
    exact T.mem_Covered.mpr ⟨d, Finset.mem_univ d, hd⟩
  · intro h p hp
    obtain ⟨d, _, hd⟩ := T.mem_Covered.mp (h hp)
    exact ⟨d, hd⟩

/-! ### Greedy selection

The algorithm is the textbook greedy for covering: take a candidate that settles the most of what is
still open, and repeat.  Two things are proved about it here -- that it stops, and that when it stops
the family it has built is admissible whenever the task is separable at all.  The approximation ratio
is a separate statement and is not claimed by anything below.

The enumeration of candidates is an explicit argument rather than an appeal to the finite type: a
solver is handed a list, its order is the only tie-break there is, and saying so keeps the algorithm
computable and the tie-break visible.
-/

/-- How many still-open pairs a candidate would settle. -/
def gain (R : Finset (Site × Site)) (d : Cand) : ℕ := (T.Cov d ∩ R).card

end Task

/-- The earliest candidate of maximal value, or `none` when every candidate is worth nothing. -/
def bestOf (f : Cand → ℕ) : List Cand → Option Cand
  | [] => none
  | d :: ds =>
    match bestOf f ds with
    | none => if 0 < f d then some d else none
    | some e => if f e ≤ f d then some d else some e

theorem bestOf_eq_none {f : Cand → ℕ} :
    ∀ {l : List Cand}, bestOf f l = none → ∀ e ∈ l, f e = 0 := by
  intro l
  induction l with
  | nil => intro _ e he; cases he
  | cons a ds ih =>
      intro h e he
      cases hds : bestOf f ds with
      | none =>
          simp only [bestOf, hds] at h
          by_cases ha : 0 < f a
          · rw [if_pos ha] at h; simp at h
          · have ha0 : f a = 0 := Nat.eq_zero_of_not_pos ha
            rcases List.mem_cons.mp he with rfl | he'
            · exact ha0
            · exact ih hds e he'
      | some b =>
          simp only [bestOf, hds] at h
          by_cases hba : f b ≤ f a
          · rw [if_pos hba] at h; simp at h
          · rw [if_neg hba] at h; simp at h

theorem bestOf_spec {f : Cand → ℕ} :
    ∀ {l : List Cand} {d : Cand}, bestOf f l = some d → 0 < f d ∧ ∀ e ∈ l, f e ≤ f d := by
  intro l
  induction l with
  | nil => intro d h; simp [bestOf] at h
  | cons a ds ih =>
      intro d h
      cases hds : bestOf f ds with
      | none =>
          simp only [bestOf, hds] at h
          by_cases ha : 0 < f a
          · rw [if_pos ha] at h
            have hda : a = d := by simpa using h
            subst hda
            refine ⟨ha, ?_⟩
            intro e he
            rcases List.mem_cons.mp he with rfl | he'
            · exact le_rfl
            · exact le_of_eq_of_le (bestOf_eq_none hds e he') (Nat.zero_le _)
          · rw [if_neg ha] at h; simp at h
      | some b =>
          simp only [bestOf, hds] at h
          obtain ⟨hbpos, hble⟩ := ih hds
          by_cases hba : f b ≤ f a
          · rw [if_pos hba] at h
            have hda : a = d := by simpa using h
            subst hda
            refine ⟨lt_of_lt_of_le hbpos hba, ?_⟩
            intro e he
            rcases List.mem_cons.mp he with rfl | he'
            · exact le_rfl
            · exact le_trans (hble e he') hba
          · rw [if_neg hba] at h
            have hdb : b = d := by simpa using h
            subst hdb
            refine ⟨hbpos, ?_⟩
            intro e he
            rcases List.mem_cons.mp he with rfl | he'
            · exact le_of_not_ge hba
            · exact hble e he'

variable [Fintype Site] [DecidableEq Site] [Fintype Cand] [DecidableEq Cand]

/-- One greedy run, with an explicit step budget and an explicit candidate list. -/
def greedy (T : Task Site Cand) (cands : List Cand) :
    ℕ → Finset (Site × Site) → Finset Cand → Finset Cand
  | 0, _, F => F
  | n + 1, R, F =>
    match bestOf (T.gain R) cands with
    | none => F
    | some d => greedy T cands n (R \ T.Cov d) (insert d F)

namespace Task

variable (T : Task Site Cand)

omit [Fintype Cand] in
theorem Covered_insert (d : Cand) (F : Finset Cand) :
    T.Covered (insert d F) = T.Cov d ∪ T.Covered F := by
  ext p
  constructor
  · intro hp
    obtain ⟨e, he, hpe⟩ := T.mem_Covered.mp hp
    rcases Finset.mem_insert.mp he with rfl | he'
    · exact Finset.mem_union_left _ hpe
    · exact Finset.mem_union_right _ (T.mem_Covered.mpr ⟨e, he', hpe⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with h | h
    · exact T.mem_Covered.mpr ⟨d, Finset.mem_insert_self d F, h⟩
    · obtain ⟨e, he, hpe⟩ := T.mem_Covered.mp h
      exact T.mem_Covered.mpr ⟨e, Finset.mem_insert_of_mem he, hpe⟩

omit [Fintype Cand] in
/-- **The greedy run stops with an admissible family.**  The invariant carried through the run is
that what is still open is exactly what the family chosen so far does not yet cover. -/
theorem greedy_feasible (cands : List Cand) (hall : ∀ d : Cand, d ∈ cands)
    (hsep : T.Separable) :
    ∀ (n : ℕ) (R : Finset (Site × Site)) (F : Finset Cand),
      R = T.Need \ T.Covered F → R.card ≤ n → T.Feasible (greedy T cands n R F) := by
  intro n
  induction n with
  | zero =>
      intro R F hR hcard
      have hempty : R = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      intro p hp
      by_contra hcov
      have hmem : p ∈ R := by rw [hR]; exact Finset.mem_sdiff.mpr ⟨hp, hcov⟩
      rw [hempty] at hmem
      exact absurd hmem (Finset.notMem_empty p)
  | succ n ih =>
      intro R F hR hcard
      rw [greedy]
      cases hb : bestOf (T.gain R) cands with
      | none =>
          have hzero := bestOf_eq_none hb
          have hRempty : R = ∅ := by
            by_contra hne
            obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
            have hpNeed : p ∈ T.Need := (Finset.mem_sdiff.mp (hR ▸ hp)).1
            obtain ⟨d, hd⟩ := hsep p hpNeed
            have hpos : 0 < T.gain R d :=
              Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hd, hp⟩⟩
            have h0 := hzero d (hall d)
            omega
          intro p hp
          by_contra hcov
          have hmem : p ∈ R := by rw [hR]; exact Finset.mem_sdiff.mpr ⟨hp, hcov⟩
          rw [hRempty] at hmem
          exact absurd hmem (Finset.notMem_empty p)
      | some d =>
          obtain ⟨hpos, _⟩ := bestOf_spec hb
          obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
          have hsub : R \ T.Cov d ⊂ R := by
            refine (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ?_
            exact ⟨p, (Finset.mem_inter.mp hp).2,
              fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hp).1⟩
          have hcard' : (R \ T.Cov d).card ≤ n := by
            have hlt := Finset.card_lt_card hsub
            omega
          have hR' : R \ T.Cov d = T.Need \ T.Covered (insert d F) := by
            rw [T.Covered_insert, hR]
            ext q
            simp only [Finset.mem_sdiff, Finset.mem_union]
            tauto
          exact ih _ _ hR' hcard'

omit [Fintype Cand] in
/-- The family the run returns is no larger than its step budget. -/
theorem greedy_card_le (cands : List Cand) :
    ∀ (n : ℕ) (R : Finset (Site × Site)) (F : Finset Cand),
      (greedy T cands n R F).card ≤ n + F.card := by
  intro n
  induction n with
  | zero => intro R F; simp [greedy]
  | succ n ih =>
      intro R F
      rw [greedy]
      cases hb : bestOf (T.gain R) cands with
      | none => exact Nat.le_add_left _ _
      | some d =>
          refine le_trans (ih _ _) ?_
          have hins : (insert d F).card ≤ F.card + 1 := Finset.card_insert_le d F
          omega

omit [Fintype Cand] in
/-- **The solver, and what is promised of it.**  On a separable task the greedy run returns an
admissible family after at most `Need.card` steps, and that family has at most `Need.card` members.

The bound is on the number of steps, which is what the proof states; each step inspects every
candidate against what is still open, so a run costs `O(|cands| · |Need|²)` elementary operations --
polynomial in the size of the task.  That last reading is prose about a cost model, not a theorem. -/
theorem solve_feasible (cands : List Cand) (hall : ∀ d : Cand, d ∈ cands) (hsep : T.Separable) :
    T.Feasible (greedy T cands T.Need.card T.Need ∅) ∧
      (greedy T cands T.Need.card T.Need ∅).card ≤ T.Need.card := by
  have hinit : T.Need = T.Need \ T.Covered (∅ : Finset Cand) := by
    ext p
    constructor
    · intro hp
      refine Finset.mem_sdiff.mpr ⟨hp, ?_⟩
      intro hcon
      obtain ⟨d, hd, _⟩ := T.mem_Covered.mp hcon
      exact absurd hd (Finset.notMem_empty d)
    · intro hp
      exact (Finset.mem_sdiff.mp hp).1
  refine ⟨T.greedy_feasible cands hall hsep _ _ _ hinit le_rfl, ?_⟩
  simpa using T.greedy_card_le cands T.Need.card T.Need ∅

/-! ### Monotonicity and diminishing returns

The coverage of a family is monotone and submodular.  These are the structural properties that make
a greedy choice meaningful at all: without them "take the candidate that settles the most" is a
heuristic, and with them it is an algorithm with a guarantee.

This is also where the earlier line's objective went wrong.  `blind_count` added a nuisance term to
the count of unsettled pairs, and that sum was measured to be **non-monotone** under refinement --
which is exactly the failure of the property below, and therefore exactly the moment the greedy lost
its warrant. -/

omit [Fintype Cand] [DecidableEq Cand] in
theorem Covered_mono {F G : Finset Cand} (h : F ⊆ G) : T.Covered F ⊆ T.Covered G := by
  intro p hp
  obtain ⟨d, hd, hpd⟩ := T.mem_Covered.mp hp
  exact T.mem_Covered.mpr ⟨d, h hd, hpd⟩

omit [Fintype Cand] [DecidableEq Cand] in
/-- **Monotone.** Offering more candidates never settles less. -/
theorem covered_card_mono {F G : Finset Cand} (h : F ⊆ G) :
    (T.Covered F).card ≤ (T.Covered G).card :=
  Finset.card_le_card (T.Covered_mono h)

omit [Fintype Cand] in
/-- **Diminishing returns.** A candidate is worth no less when added to a smaller family, written
without subtraction so that it is a statement about natural numbers and not about truncation. -/
theorem covered_submodular {F G : Finset Cand} (h : F ⊆ G) (d : Cand) :
    (T.Covered (insert d G)).card + (T.Covered F).card
      ≤ (T.Covered (insert d F)).card + (T.Covered G).card := by
  have hF := Finset.card_union_add_card_inter (T.Cov d) (T.Covered F)
  have hG := Finset.card_union_add_card_inter (T.Cov d) (T.Covered G)
  rw [T.Covered_insert, T.Covered_insert]
  have hmono : (T.Cov d ∩ T.Covered F).card ≤ (T.Cov d ∩ T.Covered G).card :=
    Finset.card_le_card (Finset.inter_subset_inter subset_rfl (T.Covered_mono h))
  omega

/-! ### How fast the greedy closes: the approximation guarantee

The heart of the classical bound, in integers rather than in logarithms.  If **some** family of size
`k` is admissible, then whatever is still open shrinks by a factor of at least `(k-1)/k` at every
greedy step: the `k` admissible candidates together settle everything still open, so one of them
settles at least a `k`-th of it, and the greedy takes a candidate no worse than that one.

Iterating gives `k^t · |open after t steps| ≤ (k-1)^t · |Need|`, from which a sufficient number of
steps follows for any `t` making the right side smaller than the left.  The familiar reading of that
condition -- `t ≈ k · ln |Need|` -- is an analytic corollary and is **not** proved here; it is
recorded as open in `ProofAudit.md`. -/

omit [Fintype Cand] [DecidableEq Cand] in
/-- Settling a candidate removes exactly its gain from what is open. -/
theorem card_sdiff_cov (R : Finset (Site × Site)) (d : Cand) :
    (R \ T.Cov d).card + T.gain R d = R.card := by
  have h : R \ T.Cov d = R \ (T.Cov d ∩ R) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [h]
  exact Finset.card_sdiff_add_card_eq_card Finset.inter_subset_right

omit [Fintype Cand] [DecidableEq Cand] in
/-- **Pigeonhole.** An admissible family of size `k` settles everything still open, so one of its
members settles at least a `k`-th of it, and a candidate of maximal gain settles no less. -/
theorem card_le_card_mul_gain {G : Finset Cand} (hG : T.Feasible G)
    {R : Finset (Site × Site)} (hR : R ⊆ T.Need) {d : Cand}
    (hd : ∀ e ∈ G, T.gain R e ≤ T.gain R d) :
    R.card ≤ G.card * T.gain R d := by
  have hsub : R ⊆ G.biUnion (fun e => T.Cov e ∩ R) := by
    intro p hp
    obtain ⟨e, he, hpe⟩ := T.mem_Covered.mp (hG (hR hp))
    exact Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_inter.mpr ⟨hpe, hp⟩⟩
  exact le_trans (Finset.card_le_card hsub)
    (Finset.card_biUnion_le_card_mul _ _ _ (fun e he => hd e he))

omit [Fintype Cand] [DecidableEq Cand] in
/-- **One step of decay**, stated without subtraction. -/
theorem step_decay {G : Finset Cand} (hG : T.Feasible G)
    {R : Finset (Site × Site)} (hR : R ⊆ T.Need) {d : Cand}
    (hd : ∀ e ∈ G, T.gain R e ≤ T.gain R d) :
    G.card * (R \ T.Cov d).card + R.card ≤ G.card * R.card := by
  have h1 := T.card_le_card_mul_gain hG hR hd
  have h2 := T.card_sdiff_cov R d
  have h3 : G.card * (R \ T.Cov d).card + G.card * T.gain R d = G.card * R.card := by
    rw [← Nat.mul_add, h2]
  omega

end Task

/-- What is still open after `t` greedy steps. -/
def remaining (T : Task Site Cand) (cands : List Cand) :
    ℕ → Finset (Site × Site) → Finset (Site × Site)
  | 0, R => R
  | n + 1, R =>
    match bestOf (T.gain R) cands with
    | none => R
    | some d => remaining T cands n (R \ T.Cov d)

namespace Task

variable (T : Task Site Cand)

omit [Fintype Cand] [DecidableEq Cand] in
/-- **Geometric decay.** After `t` steps, `k^t` times what is still open is at most `(k-1)^t` times
what had to be settled in the first place. -/
theorem decay {G : Finset Cand} (hG : T.Feasible G) (cands : List Cand)
    (hall : ∀ d : Cand, d ∈ cands) :
    ∀ (t : ℕ) (R : Finset (Site × Site)), R ⊆ T.Need →
      G.card ^ t * (remaining T cands t R).card ≤ (G.card - 1) ^ t * R.card := by
  intro t
  induction t with
  | zero => intro R _; simp [remaining]
  | succ n ih =>
      intro R hR
      rw [remaining]
      cases hb : bestOf (T.gain R) cands with
      | none =>
          have hRempty : R = ∅ := by
            by_contra hne
            obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
            obtain ⟨e, he, hpe⟩ := T.mem_Covered.mp (hG (hR hp))
            have hpos : 0 < T.gain R e :=
              Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hpe, hp⟩⟩
            have h0 := bestOf_eq_none hb e (hall e)
            omega
          simp [hRempty]
      | some d =>
          obtain ⟨_, hmax⟩ := bestOf_spec hb
          have hd : ∀ e ∈ G, T.gain R e ≤ T.gain R d := fun e _ => hmax e (hall e)
          have hstep := T.step_decay hG hR hd
          have hR' : R \ T.Cov d ⊆ T.Need := subset_trans Finset.sdiff_subset hR
          have hih := ih (R \ T.Cov d) hR'
          have hmul : G.card * (R \ T.Cov d).card ≤ (G.card - 1) * R.card := by
            rcases Nat.eq_zero_or_pos G.card with hk | hk
            · have hG0 : G = ∅ := Finset.card_eq_zero.mp hk
              have hRe : R = ∅ := by
                rcases Finset.eq_empty_or_nonempty R with h | ⟨p, hp⟩
                · exact h
                · have hmem := hG (hR hp)
                  rw [hG0] at hmem
                  simp [Covered] at hmem
              simp [hRe]
            · have hsm : (G.card - 1) * R.card = G.card * R.card - R.card := by
                rw [Nat.sub_mul, Nat.one_mul]
              omega
          have hstep2 : G.card * (G.card ^ n * (remaining T cands n (R \ T.Cov d)).card)
              ≤ G.card * ((G.card - 1) ^ n * (R \ T.Cov d).card) :=
            Nat.mul_le_mul_left _ hih
          have hstep3 : (G.card - 1) ^ n * (G.card * (R \ T.Cov d).card)
              ≤ (G.card - 1) ^ n * ((G.card - 1) * R.card) :=
            Nat.mul_le_mul_left _ hmul
          have e1 : G.card ^ (n + 1) * (remaining T cands n (R \ T.Cov d)).card
              = G.card * (G.card ^ n * (remaining T cands n (R \ T.Cov d)).card) := by
            rw [pow_succ, mul_comm (G.card ^ n) G.card, mul_assoc]
          have e2 : G.card * ((G.card - 1) ^ n * (R \ T.Cov d).card)
              = (G.card - 1) ^ n * (G.card * (R \ T.Cov d).card) := by
            rw [← mul_assoc, ← mul_assoc, mul_comm G.card ((G.card - 1) ^ n)]
          have e3 : (G.card - 1) ^ n * ((G.card - 1) * R.card)
              = (G.card - 1) ^ (n + 1) * R.card := by
            rw [pow_succ, ← mul_assoc, mul_comm ((G.card - 1) ^ n) (G.card - 1),
              mul_comm (G.card - 1) ((G.card - 1) ^ n)]
          rw [e1]
          refine le_trans hstep2 ?_
          rw [e2]
          exact le_trans hstep3 (le_of_eq e3)

omit [Fintype Cand] [DecidableEq Cand] in
/-- Nothing is covered by the empty family, so the run starts with everything open. -/
theorem Need_sdiff_empty : T.Need = T.Need \ T.Covered (∅ : Finset Cand) := by
  ext p
  constructor
  · intro hp
    refine Finset.mem_sdiff.mpr ⟨hp, ?_⟩
    intro hcon
    obtain ⟨d, hd, _⟩ := T.mem_Covered.mp hcon
    exact absurd hd (Finset.notMem_empty d)
  · intro hp
    exact (Finset.mem_sdiff.mp hp).1

omit [Fintype Cand] in
/-- What the run leaves open is what the family it built does not cover. -/
theorem greedy_sdiff (cands : List Cand) :
    ∀ (n : ℕ) (R : Finset (Site × Site)) (F : Finset Cand), R = T.Need \ T.Covered F →
      T.Need \ T.Covered (greedy T cands n R F) = remaining T cands n R := by
  intro n
  induction n with
  | zero => intro R F hR; rw [greedy, remaining]; exact hR.symm
  | succ n ih =>
      intro R F hR
      rw [greedy, remaining]
      cases hb : bestOf (T.gain R) cands with
      | none => exact hR.symm
      | some d =>
          refine ih _ _ ?_
          rw [T.Covered_insert, hR]
          ext q
          simp only [Finset.mem_sdiff, Finset.mem_union]
          tauto

omit [Fintype Cand] [DecidableEq Cand] in
/-- After enough steps nothing is open: `t` is enough as soon as the decay bound falls below one. -/
theorem remaining_empty_of_lt {G : Finset Cand} (hG : T.Feasible G) (cands : List Cand)
    (hall : ∀ d : Cand, d ∈ cands) (t : ℕ)
    (hlt : (G.card - 1) ^ t * T.Need.card < G.card ^ t) :
    remaining T cands t T.Need = ∅ := by
  have hdec := T.decay hG cands hall t T.Need (Finset.Subset.refl _)
  by_contra hne
  have hpos : 0 < (remaining T cands t T.Need).card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have hge : G.card ^ t ≤ G.card ^ t * (remaining T cands t T.Need).card :=
    Nat.le_mul_of_pos_right _ hpos
  omega

omit [Fintype Cand] in
/-- **The guarantee.**  If *some* admissible family has `k` members, then for every step budget `t`
with `(k-1)^t · |Need| < k^t` the greedy run returns an admissible family of at most `t` members.

This is the classical greedy bound for covering, in the form a proof assistant can carry: the
condition on `t` is the decay condition, and reading it as `t ≈ k · ln |Need|` is an analytic
corollary that is not proved here. -/
theorem solve_ratio {G : Finset Cand} (hG : T.Feasible G) (cands : List Cand)
    (hall : ∀ d : Cand, d ∈ cands) (t : ℕ)
    (hlt : (G.card - 1) ^ t * T.Need.card < G.card ^ t) :
    T.Feasible (greedy T cands t T.Need ∅) ∧ (greedy T cands t T.Need ∅).card ≤ t := by
  have h1 := T.greedy_sdiff cands t T.Need ∅ T.Need_sdiff_empty
  have h2 := T.remaining_empty_of_lt hG cands hall t hlt
  refine ⟨?_, by simpa using T.greedy_card_le cands t T.Need ∅⟩
  intro p hp
  by_contra hcov
  have hmem : p ∈ T.Need \ T.Covered (greedy T cands t T.Need ∅) :=
    Finset.mem_sdiff.mpr ⟨hp, hcov⟩
  rw [h1, h2] at hmem
  exact absurd hmem (Finset.notMem_empty p)

end Task

/-! ### From a condition on the budget to a number

`solve_ratio` says a budget `t` is enough as soon as `(k-1)^t · |Need| < k^t`.  Turning that into a
number is the classical step `(1 - 1/k)^k ≤ e⁻¹ < 1/2`, and it is done here **without** real
analysis: an integer Bernoulli inequality, proved by induction, gives `2·(k-1)^k ≤ k^k` directly, so
what is still open at least halves every `k` steps.
-/

/-- **Integer Bernoulli.**  `(a+1)^(n+1)` dominates `a^(n+1)` plus one whole extra order. -/
theorem bernoulli_nat (a : ℕ) : ∀ n : ℕ, a ^ (n + 1) + (n + 1) * a ^ n ≤ (a + 1) ^ (n + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have key : (a + 1) * (a ^ (n + 1) + (n + 1) * a ^ n)
          = a ^ (n + 2) + (n + 2) * a ^ (n + 1) + (n + 1) * a ^ n := by ring
      show a ^ (n + 2) + (n + 2) * a ^ (n + 1) ≤ (a + 1) ^ (n + 2)
      calc a ^ (n + 2) + (n + 2) * a ^ (n + 1)
          ≤ (a + 1) * (a ^ (n + 1) + (n + 1) * a ^ n) := by rw [key]; omega
        _ ≤ (a + 1) * (a + 1) ^ (n + 1) := Nat.mul_le_mul_left _ ih
        _ = (a + 1) ^ (n + 2) := by ring

/-- The halving inequality in the form `2·a^(a+1) ≤ (a+1)^(a+1)`. -/
theorem two_mul_pow_succ_le (a : ℕ) : 2 * a ^ (a + 1) ≤ (a + 1) ^ (a + 1) := by
  have hb := bernoulli_nat a a
  have h : a ^ (a + 1) ≤ (a + 1) * a ^ a := by
    calc a ^ (a + 1) = a * a ^ a := by ring
      _ ≤ (a + 1) * a ^ a := Nat.mul_le_mul_right _ (Nat.le_succ a)
  omega

/-- **Halving.**  `(1 - 1/k)^k ≤ 1/2`, stated in integers. -/
theorem two_mul_sub_pow_le {k : ℕ} (hk : 1 ≤ k) : 2 * (k - 1) ^ k ≤ k ^ k := by
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
  simpa using two_mul_pow_succ_le a

namespace Task

variable (T : Task Site Cand)

omit [Fintype Cand] [DecidableEq Cand] in
/-- A run never opens anything that was not open. -/
theorem remaining_subset (cands : List Cand) :
    ∀ (t : ℕ) (R : Finset (Site × Site)), remaining T cands t R ⊆ R := by
  intro t
  induction t with
  | zero => intro R; exact Finset.Subset.refl _
  | succ n ih =>
      intro R
      rw [remaining]
      cases hb : bestOf (T.gain R) cands with
      | none => exact Finset.Subset.refl _
      | some d => exact subset_trans (ih _) Finset.sdiff_subset

omit [Fintype Cand] [DecidableEq Cand] in
/-- When nothing gains anything, the run stands still. -/
theorem remaining_of_none (cands : List Cand) {R : Finset (Site × Site)}
    (h : bestOf (T.gain R) cands = none) : ∀ t : ℕ, remaining T cands t R = R := by
  intro t
  induction t with
  | zero => rfl
  | succ n _ => rw [remaining, h]

omit [Fintype Cand] [DecidableEq Cand] in
/-- Runs compose. -/
theorem remaining_add (cands : List Cand) :
    ∀ (a b : ℕ) (R : Finset (Site × Site)),
      remaining T cands (a + b) R = remaining T cands b (remaining T cands a R) := by
  intro a
  induction a with
  | zero => intro b R; rw [Nat.zero_add]; rfl
  | succ a ih =>
      intro b R
      rw [Nat.succ_add, remaining, remaining]
      cases hb : bestOf (T.gain R) cands with
      | none => exact (T.remaining_of_none cands hb b).symm
      | some d => exact ih b (R \ T.Cov d)

omit [Fintype Cand] [DecidableEq Cand] in
/-- **What is open at least halves every `k` steps**, where `k` is the size of any admissible
family.  This is the decay bound with the halving inequality put into it. -/
theorem halve {G : Finset Cand} (hG : T.Feasible G) (hk : 1 ≤ G.card) (cands : List Cand)
    (hall : ∀ d : Cand, d ∈ cands) {R : Finset (Site × Site)} (hR : R ⊆ T.Need) :
    2 * (remaining T cands G.card R).card ≤ R.card := by
  have hd := T.decay hG cands hall G.card R hR
  have hh := two_mul_sub_pow_le hk
  have h1 : 2 * (G.card ^ G.card * (remaining T cands G.card R).card)
      ≤ 2 * ((G.card - 1) ^ G.card * R.card) := Nat.mul_le_mul_left _ hd
  have h2 : 2 * ((G.card - 1) ^ G.card * R.card) = 2 * (G.card - 1) ^ G.card * R.card := by ring
  have h3 : 2 * (G.card - 1) ^ G.card * R.card ≤ G.card ^ G.card * R.card :=
    Nat.mul_le_mul_right _ hh
  have h4 : G.card ^ G.card * (2 * (remaining T cands G.card R).card)
      = 2 * (G.card ^ G.card * (remaining T cands G.card R).card) := by ring
  have h5 : G.card ^ G.card * (2 * (remaining T cands G.card R).card)
      ≤ G.card ^ G.card * R.card := by omega
  exact Nat.le_of_mul_le_mul_left h5 (pow_pos (by omega) G.card)

omit [Fintype Cand] [DecidableEq Cand] in
/-- Halving iterated: after `j` blocks of `k` steps, `2^j` times what is open is at most what had to
be settled in the first place. -/
theorem halve_iter {G : Finset Cand} (hG : T.Feasible G) (hk : 1 ≤ G.card) (cands : List Cand)
    (hall : ∀ d : Cand, d ∈ cands) :
    ∀ j : ℕ, 2 ^ j * (remaining T cands (j * G.card) T.Need).card ≤ T.Need.card := by
  intro j
  induction j with
  | zero => simp [remaining]
  | succ j ih =>
      have hstep : (j + 1) * G.card = j * G.card + G.card := by ring
      rw [hstep, T.remaining_add cands]
      have hsub : remaining T cands (j * G.card) T.Need ⊆ T.Need :=
        T.remaining_subset cands _ _
      have hhalf := T.halve hG hk cands hall hsub
      have hmul : 2 ^ j * (2 * (remaining T cands G.card
          (remaining T cands (j * G.card) T.Need)).card)
          ≤ 2 ^ j * (remaining T cands (j * G.card) T.Need).card :=
        Nat.mul_le_mul_left _ hhalf
      have he : 2 ^ (j + 1) * (remaining T cands G.card
          (remaining T cands (j * G.card) T.Need)).card
          = 2 ^ j * (2 * (remaining T cands G.card
              (remaining T cands (j * G.card) T.Need)).card) := by ring
      omega

omit [Fintype Cand] in
/-- **The number.**  If some admissible family has `k ≥ 1` members, the greedy run needs at most
`k · (1 + log₂ |Need|)` steps and returns an admissible family of at most that many members.

This is the classical `k · O(log |Need|)` bound for greedy covering, obtained here without any
analysis: the halving inequality `2·(k-1)^k ≤ k^k` is an integer Bernoulli estimate. -/
theorem solve_log {G : Finset Cand} (hG : T.Feasible G) (hk : 1 ≤ G.card) (cands : List Cand)
    (hall : ∀ d : Cand, d ∈ cands) :
    T.Feasible (greedy T cands ((Nat.log 2 T.Need.card + 1) * G.card) T.Need ∅) ∧
      (greedy T cands ((Nat.log 2 T.Need.card + 1) * G.card) T.Need ∅).card
        ≤ (Nat.log 2 T.Need.card + 1) * G.card := by
  set j := Nat.log 2 T.Need.card + 1 with hj
  have hlt : T.Need.card < 2 ^ j := Nat.lt_pow_succ_log_self (by norm_num) _
  have hbound := T.halve_iter hG hk cands hall j
  have hempty : remaining T cands (j * G.card) T.Need = ∅ := by
    by_contra hne
    have hpos : 0 < (remaining T cands (j * G.card) T.Need).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    have hge : 2 ^ j ≤ 2 ^ j * (remaining T cands (j * G.card) T.Need).card :=
      Nat.le_mul_of_pos_right _ hpos
    omega
  have h1 := T.greedy_sdiff cands (j * G.card) T.Need ∅ T.Need_sdiff_empty
  refine ⟨?_, by simpa using T.greedy_card_le cands (j * G.card) T.Need ∅⟩
  intro p hp
  by_contra hcov
  have hmem : p ∈ T.Need \ T.Covered (greedy T cands (j * G.card) T.Need ∅) :=
    Finset.mem_sdiff.mpr ⟨hp, hcov⟩
  rw [h1, hempty] at hmem
  exact absurd hmem (Finset.notMem_empty p)

end Task

/-! ### What the run costs

Saying "polynomial" is prose until an elementary operation is named and counted.  The one the
algorithm actually repeats is evaluating a candidate's gain, so that is the unit here: `greedyCost`
counts gain evaluations along exactly the recursion of `greedy`, and the bound below is a theorem
about the algorithm rather than a remark about it.

What remains a modelling decision, and is recorded as such in `ProofAudit.md`: identifying one gain
evaluation with a bounded number of machine operations.  Nothing in Lean can settle that, because
Lean has no machine.
-/

/-- The gain evaluations the run performs, counted along its own recursion. -/
def greedyCost (T : Task Site Cand) (cands : List Cand) :
    ℕ → Finset (Site × Site) → ℕ
  | 0, _ => 0
  | n + 1, R =>
    match bestOf (T.gain R) cands with
    | none => cands.length
    | some d => cands.length + greedyCost T cands n (R \ T.Cov d)

namespace Task

variable (T : Task Site Cand)

omit [Fintype Cand] [DecidableEq Cand] in
/-- Each step evaluates every candidate once, so the run costs at most budget times candidates. -/
theorem greedyCost_le (cands : List Cand) :
    ∀ (n : ℕ) (R : Finset (Site × Site)), greedyCost T cands n R ≤ n * cands.length := by
  intro n
  induction n with
  | zero => intro R; rw [greedyCost]; omega
  | succ n ih =>
      intro R
      cases hb : bestOf (T.gain R) cands with
      | none =>
          simp only [greedyCost, hb]
          exact Nat.le_mul_of_pos_left _ (by omega)
      | some d =>
          simp only [greedyCost, hb]
          have h := ih (R \ T.Cov d)
          have he : (n + 1) * cands.length = cands.length + n * cands.length := by ring
          omega

omit [DecidableEq Site] [Fintype Cand] [DecidableEq Cand] in
/-- The pairs to separate are at most the pairs there are. -/
theorem Need_card_le : T.Need.card ≤ Fintype.card Site * Fintype.card Site := by
  have h : T.Need.card ≤ Fintype.card (Site × Site) := Finset.card_le_univ _
  simpa [Fintype.card_prod] using h

omit [Fintype Cand] [DecidableEq Cand] in
/-- **The cost of the solver.**  A run with the budget `solve_log` needs -- that is, `k` times one
plus the bits of `|Need|`, where `k` is the size of any admissible family -- evaluates at most
`k · (1 + log₂ (n·n)) · |cands|` gains, `n` being the number of sites.

The bound holds for **any** budget of that shape and needs no hypothesis about the task: every factor
is a size of the task, so the count is polynomial in it.  That is the sense in which the solver is
polynomial, and it is now a statement about a counted quantity rather than about an intention. -/
theorem solve_cost (k : ℕ) (cands : List Cand) :
    greedyCost T cands ((Nat.log 2 T.Need.card + 1) * k) T.Need
      ≤ (Nat.log 2 (Fintype.card Site * Fintype.card Site) + 1) * k * cands.length := by
  have h1 := T.greedyCost_le cands ((Nat.log 2 T.Need.card + 1) * k) T.Need
  have h2 : Nat.log 2 T.Need.card ≤ Nat.log 2 (Fintype.card Site * Fintype.card Site) :=
    Nat.log_mono_right T.Need_card_le
  have h3 : (Nat.log 2 T.Need.card + 1) * k
      ≤ (Nat.log 2 (Fintype.card Site * Fintype.card Site) + 1) * k :=
    Nat.mul_le_mul_right _ (by omega)
  exact le_trans h1 (Nat.mul_le_mul_right _ h3)

/-! ### Transfer: what the revealed pairs say about the rest

`no_transferFailure` shows that covering what was revealed says nothing about the rest **in general**.
The honest question is therefore what has to hold of the revealed part for it to say something, and
the answer is exact: the revealed pairs must realise every **signature** — every set of candidates
that separates a pair.  That is the corpus's P5 made into a condition one can check.
-/

/-- Which candidates separate a pair: the only thing about a pair that a solver can use. -/
def sig (p : Site × Site) : Finset Cand :=
  Finset.univ.filter fun d => T.dist d p.1 ≠ T.dist d p.2

omit [Fintype Site] [DecidableEq Site] [DecidableEq Cand] in
@[simp] theorem mem_sig {d : Cand} {p : Site × Site} :
    d ∈ T.sig p ↔ T.dist d p.1 ≠ T.dist d p.2 := by
  simp [sig, Finset.mem_filter]

/-- A revealed set of pairs is **representative** when every pair that must be separated has its
signature realised among the revealed ones. -/
def Representative (S : Finset (Site × Site)) : Prop :=
  ∀ p ∈ T.Need, ∃ q ∈ S, T.sig q = T.sig p

omit [DecidableEq Cand] in
/-- **Transfer, with its condition.**  Covering a representative sample covers everything.  This is
the exact counterpart of `no_transferFailure`: without representativeness the implication fails, and
with it the implication holds. -/
theorem feasible_of_representative {S : Finset (Site × Site)} {F : Finset Cand}
    (hrep : T.Representative S) (hS : S ⊆ T.Covered F) : T.Feasible F := by
  intro p hp
  obtain ⟨q, hqS, hsig⟩ := hrep p hp
  obtain ⟨d, hdF, hqd⟩ := T.mem_Covered.mp (hS hqS)
  have hdq : d ∈ T.sig q := T.mem_sig.mpr (T.mem_Cov.mp hqd).2
  rw [hsig] at hdq
  exact T.mem_Covered.mpr ⟨d, hdF, T.mem_Cov.mpr ⟨T.mem_Need.mp hp, T.mem_sig.mp hdq⟩⟩

/-- **A representative sample is always small.**  There are at most `2^|Cand|` signatures, so one
pair per realised signature is a representative sample of at most that size -- the sample complexity
of transfer is bounded by the frozen hypothesis class and by nothing about the source. -/
theorem exists_representative :
    ∃ S : Finset (Site × Site), S ⊆ T.Need ∧ T.Representative S ∧
      S.card ≤ 2 ^ Fintype.card Cand := by
  classical
  rcases Finset.eq_empty_or_nonempty T.Need with hE | ⟨p0, hp0⟩
  · refine ⟨∅, by simp, ?_, by simp⟩
    intro p hp
    rw [hE] at hp
    exact absurd hp (Finset.notMem_empty p)
  · set pick : Finset Cand → Site × Site := fun b =>
      if h : ∃ p ∈ T.Need, T.sig p = b then h.choose else p0 with hpick
    have hpick_mem : ∀ b ∈ T.Need.image T.sig, pick b ∈ T.Need ∧ T.sig (pick b) = b := by
      intro b hb
      obtain ⟨p, hp, hsp⟩ := Finset.mem_image.mp hb
      have hex : ∃ p ∈ T.Need, T.sig p = b := ⟨p, hp, hsp⟩
      simp only [hpick, dif_pos hex]
      exact ⟨hex.choose_spec.1, hex.choose_spec.2⟩
    refine ⟨(T.Need.image T.sig).image pick, ?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
      exact (hpick_mem b hb).1
    · intro p hp
      have hb : T.sig p ∈ T.Need.image T.sig := Finset.mem_image.mpr ⟨p, hp, rfl⟩
      exact ⟨pick (T.sig p), Finset.mem_image.mpr ⟨T.sig p, hb, rfl⟩, (hpick_mem _ hb).2⟩
    · refine le_trans Finset.card_image_le ?_
      exact le_trans (Finset.card_le_univ _) (le_of_eq Fintype.card_finset)


/-! ### The witnessed cut

`feasible_of_representative` says what has to hold of the revealed part for covering it to say
anything.  It was proved and then not used: the solver cut its merge forest wherever no *revealed*
role objected, which leaves a query site free to be absorbed into any block at all, and measurement
showed exactly that -- the quotient reaches its proved optimum and the guarantee becomes empty.

What follows is the cut the condition dictates.  A signature is **safe** for a revealed sample when
no revealed pair carrying it is separated by the target; a merge is admitted only at a safe
signature.  The theorem below is the reason that is not one more rule of thumb: on a *representative*
sample drawn from `Need` -- and `exists_representative` produces exactly such a sample, of size at
most `2 ^ |Cand|` -- the resulting equivalence refines the target, so the answer is exact wherever it
speaks.  The hypothesis `S ⊆ T.Need` is doing the work and cannot be dropped: it is what makes a
witness of a signature a witness that the signature *separates*.
-/

/-- A signature no revealed pair contradicts: every revealed pair carrying it is left unseparated by
the target. -/
def Safe (S : Finset (Site × Site)) (g : Finset Cand) : Prop :=
  ∀ p ∈ S, T.sig p = g → T.target p.1 = T.target p.2

/-- The witnessed cut: glue along pairs whose signature is safe, and close up. -/
def witness (S : Finset (Site × Site)) : Setoid Site :=
  Relation.EqvGen.setoid fun x y => T.Safe S (T.sig (x, y))

omit [DecidableEq Site] [DecidableEq Cand] in
/-- **The witnessed cut is admissible.**  Against a representative sample of pairs that genuinely
need separating, gluing only at safe signatures never glues two different answers -- including at
sites the sample says nothing about, which is the case the unwitnessed cut got wrong. -/
theorem witness_le_ker {S : Finset (Site × Site)}
    (hS : S ⊆ T.Need) (hrep : T.Representative S) :
    T.witness S ≤ Setoid.ker T.target := by
  intro x y hxy
  show T.target x = T.target y
  induction hxy with
  | rel a b hab =>
      by_contra hne
      obtain ⟨q, hqS, hsig⟩ := hrep (a, b) (T.mem_Need.mpr hne)
      exact absurd (hab q hqS hsig) (T.mem_Need.mp (hS hqS))
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ hab hbc => exact hab.trans hbc

omit [Fintype Site] [DecidableEq Site] [DecidableEq Cand] in
/-- More revealed pairs can only make a signature harder to call safe, so the cut gets finer.  This
is what licenses the implementation, which tests **every** revealed pair rather than a representative
subsample: it computes a refinement of the cut the theorem is about. -/
theorem witness_mono {S S' : Finset (Site × Site)} (h : S ⊆ S') :
    T.witness S' ≤ T.witness S := by
  intro x y hxy
  exact Relation.EqvGen.mono (fun a b hab p hp => hab p (h hp)) hxy

omit [DecidableEq Site] [DecidableEq Cand] in
/-- **Admissibility for the cut the code actually computes.**  It suffices that the revealed pairs
*contain* a representative sample of what needs separating; they may contain anything else besides. -/
theorem witness_le_ker_of_subset {S R : Finset (Site × Site)}
    (hSR : S ⊆ R) (hS : S ⊆ T.Need) (hrep : T.Representative S) :
    T.witness R ≤ Setoid.ker T.target :=
  le_trans (T.witness_mono hSR) (witness_le_ker T hS hrep)

/-! #### The one checkable form of the hypothesis, and why it is empty

`Representative` quantifies over `Need`, and `Need` mentions the target at **every** site, the query's
included; so the hypothesis of `witness_le_ker` cannot be checked while solving.  There is exactly one
way to make it checkable: ask that every signature occurring **anywhere** be carried by a revealed pair
that the target separates.  That mentions no unrevealed target and is decidable.

Both halves are below, and the second is the answer to "why is the guarantee not cashed in":
the condition is sufficient (`witness_le_ker_of_sigCovered`) and it holds **only** when the cut glues
nothing at all (`witness_discrete_of_sigCovered`).  A signature carried by a separated revealed pair is
a signature at which `Safe` is false, i.e. exactly one the cut refuses; so demanding it of every
signature demands that every merge be refused.  The checkable form of transfer is equivalent to no
transfer -- which is the corpus's P5 stated for this theory, and a theorem rather than a caution. -/

/-- Every signature that occurs at all is carried by a revealed pair the target separates.  Decidable,
and mentioning no target the solver does not have. -/
def SigCovered (S : Finset (Site × Site)) : Prop :=
  ∀ p : Site × Site, ∃ q ∈ S, q ∈ T.Need ∧ T.sig q = T.sig p

omit [DecidableEq Cand] in
/-- The separated part of a sample that covers every signature is representative. -/
theorem representative_of_sigCovered {S : Finset (Site × Site)} (hc : T.SigCovered S) :
    T.Representative (S.filter fun q => q ∈ T.Need) := by
  intro p _
  obtain ⟨q, hqS, hqN, hsig⟩ := hc p
  exact ⟨q, Finset.mem_filter.mpr ⟨hqS, hqN⟩, hsig⟩

omit [DecidableEq Cand] in
/-- **Sufficient.**  Under the checkable condition the witnessed cut refines the target. -/
theorem witness_le_ker_of_sigCovered {S : Finset (Site × Site)} (hc : T.SigCovered S) :
    T.witness S ≤ Setoid.ker T.target :=
  witness_le_ker_of_subset T (Finset.filter_subset _ _)
    (fun _ hq => (Finset.mem_filter.mp hq).2) (T.representative_of_sigCovered hc)

omit [DecidableEq Site] [DecidableEq Cand] in
/-- **And empty.**  Under the same condition the cut glues nothing: two sites it identifies are the
same site.  So the only form of representativeness a solver can verify certifies precisely the runs in
which it transfers nothing, and the gap of `gap_feasibleOn_not_feasible` is not closable by checking. -/
theorem witness_discrete_of_sigCovered {S : Finset (Site × Site)} (hc : T.SigCovered S)
    {x y : Site} (h : (T.witness S).r x y) : x = y := by
  induction h with
  | rel a b hab =>
      obtain ⟨q, hqS, hqN, hsig⟩ := hc (a, b)
      exact absurd (hab q hqS hsig) (T.mem_Need.mp hqN)
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ hab hbc => exact hab.trans hbc

/-- **The cut the code actually computes.**  `witness` is the closure of the safe merges alone, but the
solver also glues, unconditionally, any two revealed sites the question calls the same -- that is
extensionality (`Extensional`), and it is not optional: it is half of `K_o = E`.  Those generators lie in
`ker target` by definition, so the guarantee survives them untouched, and this is the statement that covers
the shipped construction rather than an idealisation of it. -/
def witnessExt (S : Finset (Site × Site)) (O : Finset Site) : Setoid Site :=
  Relation.EqvGen.setoid fun x y =>
    T.Safe S (T.sig (x, y)) ∨ (x ∈ O ∧ y ∈ O ∧ T.target x = T.target y)

omit [DecidableEq Site] [DecidableEq Cand] in
/-- **Admissible, with extensionality's merges included.** -/
theorem witnessExt_le_ker {S : Finset (Site × Site)} (O : Finset Site)
    (hS : S ⊆ T.Need) (hrep : T.Representative S) :
    T.witnessExt S O ≤ Setoid.ker T.target := by
  intro x y hxy
  show T.target x = T.target y
  induction hxy with
  | rel a b hab =>
      rcases hab with hsafe | ⟨_, _, heq⟩
      · by_contra hne
        obtain ⟨q, hqS, hsig⟩ := hrep (a, b) (T.mem_Need.mpr hne)
        exact absurd (hsafe q hqS hsig) (T.mem_Need.mp (hS hqS))
      · exact heq
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ hab hbc => exact hab.trans hbc

omit [DecidableEq Cand] in
/-- Feasibility in the covering language, for the witnessed cut: the theory's bridge applies to it
exactly as it does to a chosen subfamily. -/
theorem witness_feasible {S : Finset (Site × Site)} {F : Finset Cand}
    (hS : S ⊆ T.Need) (hrep : T.Representative S) (hle : T.agree F ≤ T.witness S) :
    T.Feasible F :=
  (T.feasible_iff_le_ker F).mpr (le_trans hle (witness_le_ker T hS hrep))

end Task

namespace Task

variable (T : Task Site Cand)

/-! ### The whole theory, in four statements

Everything else in this file is machinery.  These four are the theory, and they are stated together
so that what is claimed can be read in one place.

1. **Universality.**  Every task has an admissible observation: naming the site is one
   (`separable_of_injective`).  So no task is outside the class and none may be refused.
2. **Totality.**  The answer is a total function of the site (`answerFrom`), exact at every site
   whose block was revealed (`answerFrom_eq_target`).
3. **Completeness on revealed blocks.**  If the teachers revealed every block, the answer is exactly
   right everywhere (`exact_of_all_revealed`).
4. **The price, and hence the only objective.**  What is left unvouched is bounded by the size of the
   quotient minus what the teachers showed (`unvouched_blocks_le`).  Since universality is bought by
   the *discrete* observation, whose quotient is maximal, universality and transfer pull against each
   other, and the whole problem is the single quantity `nblocks`.

There is no menu here and no parameter to choose: a representation is admissible or it is not, and
among the admissible ones the theory prefers exactly one thing -- the coarsest.  Every apparatus
outside this file (which distinctions are offered, how a target is encoded) is a **search space** for
that one minimisation, not a part of the theory.
-/

/-! ### The size of the quotient

`solve_log` bounds the **number of chosen distinctions**, and a run over 799 tasks showed that this
is the wrong quantity: the greedy took one maximally fine level -- optimal for that objective, and
useless, since almost every block of the answer was one the teachers never showed.

What matters is the size of the **quotient**, because that is what the teachers must have covered.
This section says how the two are related and what the quotient's size costs.
-/

/-- The block of a site under a chosen family, as a comparable value. -/
def blockKey (F : Finset Cand) (i : Site) : Cand → ℕ :=
  fun d => if d ∈ F then T.dist d i else 0

omit [Fintype Site] [DecidableEq Site] [Fintype Cand] in
theorem blockKey_eq_iff {F : Finset Cand} {i j : Site} :
    T.blockKey F i = T.blockKey F j ↔ (T.agree F).r i j := by
  constructor
  · intro h d hd
    have := congrFun h d
    simpa [blockKey, hd] using this
  · intro h
    funext d
    by_cases hd : d ∈ F
    · simp [blockKey, hd, h d hd]
    · simp [blockKey, hd]

/-- How many blocks a family cuts the sites into. -/
def nblocks (F : Finset Cand) : ℕ := (Finset.univ.image (T.blockKey F)).card

/-- How many values one candidate realises: its own contribution to the size of the quotient. -/
def spread (d : Cand) : ℕ := (Finset.univ.image (T.dist d)).card

omit [DecidableEq Site] in
/-- **Monotone.** Fewer distinctions never make the quotient finer, so pruning a family that stays
admissible can only shrink the quotient -- and an optimum may always be sought among the families no
proper subfamily of which is admissible. -/
theorem nblocks_mono {F G : Finset Cand} (h : F ⊆ G) : T.nblocks F ≤ T.nblocks G := by
  classical
  have hmap : Finset.univ.image (T.blockKey F)
      = (Finset.univ.image (T.blockKey G)).image
          (fun k => fun d => if d ∈ F then k d else 0) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨T.blockKey G i, ⟨i, rfl⟩, ?_⟩
      funext d
      by_cases hd : d ∈ F
      · simp [blockKey, hd, h hd]
      · simp [blockKey, hd]
    · rintro ⟨k, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      funext d
      by_cases hd : d ∈ F
      · simp [blockKey, hd, h hd]
      · simp [blockKey, hd]
  rw [nblocks, hmap]
  exact Finset.card_image_le

omit [DecidableEq Site] in
/-- **The quotient is no larger than the product of what its members realise.**

This is the bridge from a *family* to a *quotient*: a block is a tuple of values, so there are at
most as many blocks as there are tuples.  It is also why weighting a candidate by the values it
realises -- its description length -- is the objective that bounds the quotient, where counting
candidates does not. -/
theorem nblocks_le_prod (F : Finset Cand) : T.nblocks F ≤ ∏ d ∈ F, T.spread d := by
  classical
  induction F using Finset.induction with
  | empty =>
      have h : T.nblocks (∅ : Finset Cand) ≤ 1 := by
        rw [nblocks]
        have hsub : Finset.univ.image (T.blockKey (∅ : Finset Cand))
            ⊆ ({(fun _ => 0 : Cand → ℕ)} : Finset (Cand → ℕ)) := ?_
        · simpa using Finset.card_le_card hsub
        intro v hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        refine Finset.mem_singleton.mpr ?_
        funext d
        simp [blockKey]
      simpa using h
  | insert d F hd ih =>
      have hsplit : Finset.univ.image (T.blockKey (insert d F))
          = (Finset.univ.image (fun i => (T.blockKey F i, T.dist d i))).image
              (fun p => fun c => if c = d then p.2 else p.1 c) := by
        ext v
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, rfl⟩
          refine ⟨(T.blockKey F i, T.dist d i), ⟨i, rfl⟩, ?_⟩
          funext c
          by_cases hc : c = d
          · subst hc; simp [blockKey]
          · by_cases hcF : c ∈ F <;> simp [blockKey, hc, hcF]
        · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
          refine ⟨i, ?_⟩
          funext c
          by_cases hc : c = d
          · subst hc; simp [blockKey]
          · by_cases hcF : c ∈ F <;> simp [blockKey, hc, hcF]
      have hpair : (Finset.univ.image (fun i => (T.blockKey F i, T.dist d i))).card
          ≤ T.nblocks F * T.spread d := by
        have hsub : Finset.univ.image (fun i => (T.blockKey F i, T.dist d i))
            ⊆ (Finset.univ.image (T.blockKey F)) ×ˢ (Finset.univ.image (T.dist d)) := by
          intro p hp
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
          exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
            Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
        calc (Finset.univ.image (fun i => (T.blockKey F i, T.dist d i))).card
            ≤ ((Finset.univ.image (T.blockKey F)) ×ˢ
                (Finset.univ.image (T.dist d))).card := Finset.card_le_card hsub
          _ = T.nblocks F * T.spread d := Finset.card_product _ _
      rw [Finset.prod_insert hd]
      calc T.nblocks (insert d F) ≤ (Finset.univ.image
              (fun i => (T.blockKey F i, T.dist d i))).card := by
            rw [nblocks, hsplit]; exact Finset.card_image_le
        _ ≤ T.nblocks F * T.spread d := hpair
        _ ≤ T.spread d * ∏ x ∈ F, T.spread x := by
            rw [Nat.mul_comm]
            exact Nat.mul_le_mul_left _ ih

/-- **Pruning is complete, not merely safe.**  Every admissible family contains an admissible one no
proper subfamily of which is admissible, and its quotient is no larger.  So an optimum may always be
sought among minimal families, and dropping what is not needed never costs anything. -/
theorem exists_minimal_feasible {F : Finset Cand} (hF : T.Feasible F) :
    ∃ G ⊆ F, T.Feasible G ∧ (∀ d ∈ G, ¬ T.Feasible (G.erase d)) ∧ T.nblocks G ≤ T.nblocks F := by
  classical
  induction F using Finset.strongInduction with
  | _ F ih =>
      by_cases hmin : ∀ d ∈ F, ¬ T.Feasible (F.erase d)
      · exact ⟨F, Finset.Subset.refl _, hF, hmin, le_rfl⟩
      · push_neg at hmin
        obtain ⟨d, hdF, hd⟩ := hmin
        obtain ⟨G, hGsub, hGfeas, hGmin, hGle⟩ :=
          ih (F.erase d) (Finset.erase_ssubset hdF) hd
        exact ⟨G, subset_trans hGsub (Finset.erase_subset d F), hGfeas, hGmin,
          le_trans hGle (T.nblocks_mono (Finset.erase_subset d F))⟩

open Classical in
/-- **The optimum, named.**  An admissible quotient has at least as many blocks as the target has
values, because the target is constant on a block and every value is taken.

So the best possible is `nblocks = ` the number of distinct targets, and that happens exactly when
the observation glues precisely what the target glues.  The objective of the whole theory is
therefore two-sided and has no free part: **separate what the target separates, glue what it does
not**.  How far a representation is from the optimum is then a measured number, not an opinion. -/
theorem card_targets_le_nblocks {F : Finset Cand} (hF : T.Feasible F) :
    (Finset.univ.image T.target).card ≤ T.nblocks F := by
  set g : (Cand → ℕ) → ℕ := fun k =>
    if h : ∃ i : Site, T.blockKey F i = k then T.target h.choose else 0 with hg
  have hgk : ∀ i : Site, g (T.blockKey F i) = T.target i := by
    intro i
    have hex : ∃ j : Site, T.blockKey F j = T.blockKey F i := ⟨i, rfl⟩
    have : g (T.blockKey F i) = T.target hex.choose := by simp [hg, dif_pos hex]
    rw [this]
    exact (T.feasible_iff_le_ker F).mp hF (T.blockKey_eq_iff.mp hex.choose_spec)
  have himg : Finset.univ.image T.target ⊆ (Finset.univ.image (T.blockKey F)).image g := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨T.blockKey F i,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hgk i⟩
  exact le_trans (Finset.card_le_card himg) Finset.card_image_le

open Classical in
omit [DecidableEq Site] in
/-- **What the quotient's size buys: a bound on how much is left unanswered.**

The blocks that no revealed site inhabits are disjoint from the blocks that some revealed site
inhabits, so together they fit inside the quotient.  Hence the sites the run cannot vouch for occupy
at most `nblocks F` minus the blocks the teachers showed -- and shrinking the quotient shrinks
exactly that.  This is why the objective belongs over the quotient and not over the family. -/
theorem unvouched_blocks_le (F : Finset Cand) (Rev : Finset Site) :
    ((Finset.univ.filter (fun i => ¬ ∃ j ∈ Rev, (T.agree F).r i j)).image (T.blockKey F)).card
      + (Rev.image (T.blockKey F)).card ≤ T.nblocks F := by
  set U := Finset.univ.filter (fun i => ¬ ∃ j ∈ Rev, (T.agree F).r i j) with hU
  have hdisj : Disjoint (U.image (T.blockKey F)) (Rev.image (T.blockKey F)) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hv'
    have : (T.agree F).r i j := T.blockKey_eq_iff.mp hji.symm
    exact ((Finset.mem_filter.mp (hU ▸ hi)).2) ⟨j, hj, this⟩
  have hsub : (U.image (T.blockKey F)) ∪ (Rev.image (T.blockKey F))
      ⊆ Finset.univ.image (T.blockKey F) := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  calc ((U.image (T.blockKey F)).card + (Rev.image (T.blockKey F)).card)
      = ((U.image (T.blockKey F)) ∪ (Rev.image (T.blockKey F))).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ T.nblocks F := Finset.card_le_card hsub

/-! ### The carrier is ordered, and that is what makes the search convex

Taken from the earlier line's Stage105-107 (`usys-main/docs/usys-v2`), which established the shape
of the argument: when the states of a language are the **upward-closed filters** of a refinement
poset, their exact convex hull is the order polytope `0 ≤ x ≤ 1`, `x_i ≤ x_j`, every point of which
is a convex combination of genuine states; a linear functional is then optimised exactly by maximum
closure -- one minimum cut -- instead of by enumeration.  Where the incidence matrix is in addition
totally unimodular, arbitrary linear optimisation is exact without rounding.

What that line built intuitively, this one can state: the order needed is already here, because
**a finer distinction separates more pairs**.  That single monotonicity is what puts admissibility
into the ordered-hitting form the convex machinery needs, and it is proved rather than assumed.
-/

/-- `d'` is at least as fine as `d`: wherever `d'` cannot tell two sites apart, neither can `d`. -/
def Finer (d' d : Cand) : Prop := ∀ x y : Site, T.dist d' x = T.dist d' y → T.dist d x = T.dist d y

omit [Fintype Site] [DecidableEq Site] [Fintype Cand] [DecidableEq Cand] in
theorem finer_refl (d : Cand) : T.Finer d d := fun _ _ h => h

omit [Fintype Site] [DecidableEq Site] [Fintype Cand] [DecidableEq Cand] in
theorem finer_trans {a b c : Cand} (hab : T.Finer a b) (hbc : T.Finer b c) : T.Finer a c :=
  fun x y h => hbc x y (hab x y h)

omit [DecidableEq Site] [Fintype Cand] [DecidableEq Cand] in
/-- **A finer distinction separates more.**  The monotonicity that orders the carrier. -/
theorem Cov_mono {d' d : Cand} (h : T.Finer d' d) : T.Cov d ⊆ T.Cov d' := by
  intro p hp
  obtain ⟨hne, hsep⟩ := T.mem_Cov.mp hp
  refine T.mem_Cov.mpr ⟨hne, ?_⟩
  intro heq
  exact hsep (h p.1 p.2 heq)

omit [Fintype Cand] [DecidableEq Cand] in
/-- **Admissibility is upward closed along the order.**  Replacing every chosen distinction by one
at least as fine keeps the family admissible -- so the admissible families are a filter of the
refinement poset, which is the form the convex machinery requires. -/
theorem feasible_of_finer {F G : Finset Cand} (hF : T.Feasible F)
    (h : ∀ d ∈ F, ∃ d' ∈ G, T.Finer d' d) : T.Feasible G := by
  intro p hp
  obtain ⟨d, hdF, hpd⟩ := T.mem_Covered.mp (hF hp)
  obtain ⟨d', hd'G, hfin⟩ := h d hdF
  exact T.mem_Covered.mpr ⟨d', hd'G, T.Cov_mono hfin hpd⟩

omit [DecidableEq Cand] in
/-- **Admissibility is exactly a hitting problem.**  Each pair that must be separated names the set
of distinctions that separate it -- its signature -- and a family is admissible exactly when it hits
every such set.  With `Cov_mono` these sets are upward closed, which is the ordered-hitting form of
Stage106 and the input to the integrality question of Stage107. -/
theorem feasible_iff_hits {F : Finset Cand} :
    T.Feasible F ↔ ∀ p ∈ T.Need, ∃ d ∈ F, d ∈ T.sig p := by
  constructor
  · intro hF p hp
    obtain ⟨d, hdF, hpd⟩ := T.mem_Covered.mp (hF hp)
    exact ⟨d, hdF, T.mem_sig.mpr (T.mem_Cov.mp hpd).2⟩
  · intro h p hp
    obtain ⟨d, hdF, hd⟩ := h p hp
    exact T.mem_Covered.mpr ⟨d, hdF, T.mem_Cov.mpr ⟨T.mem_Need.mp hp, T.mem_sig.mp hd⟩⟩

omit [Fintype Site] [DecidableEq Site] [Fintype Cand] in
/-- The finest member of a chain of distinctions. -/
theorem exists_finest : ∀ (F : Finset Cand), F.Nonempty →
    (∀ a ∈ F, ∀ b ∈ F, T.Finer a b ∨ T.Finer b a) → ∃ d ∈ F, ∀ e ∈ F, T.Finer d e := by
  classical
  intro F
  induction F using Finset.induction with
  | empty => intro h _; exact absurd rfl (Finset.nonempty_iff_ne_empty.mp h)
  | insert a S haS ih =>
      intro _ hchain
      by_cases hS : S.Nonempty
      · obtain ⟨b, hbS, hb⟩ := ih hS (fun x hx y hy =>
          hchain x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy))
        rcases hchain a (Finset.mem_insert_self a S) b (Finset.mem_insert_of_mem hbS) with h | h
        · refine ⟨a, Finset.mem_insert_self a S, fun e he => ?_⟩
          rcases Finset.mem_insert.mp he with rfl | he'
          · exact T.finer_refl e
          · exact T.finer_trans h (hb e he')
        · refine ⟨b, Finset.mem_insert_of_mem hbS, fun e he => ?_⟩
          rcases Finset.mem_insert.mp he with rfl | he'
          · exact h
          · exact hb e he'
      · refine ⟨a, Finset.mem_insert_self a S, fun e he => ?_⟩
        rcases Finset.mem_insert.mp he with rfl | he'
        · exact T.finer_refl e
        · exact absurd ⟨e, he'⟩ hS

omit [Fintype Cand] in
/-- **On a chain the search collapses to a scan: there is no exponent at all.**

If the offered distinctions are totally ordered by fineness, the finest member of an admissible
family is admissible by itself.  So an optimum is a **single** distinction, found by walking the
chain from the coarse end -- no subset search, no relaxation, no rounding.

This is the strongest form the convex-carrier argument takes, and it explains what the runs show:
the solver picks one distinction on 379 of 379 cases, because on a chain that is what an optimum
looks like.  It also prices enriching the language exactly: distinctions that are **not** comparable
break the chain, and the ordered-hitting problem returns with them. -/
theorem exists_single_of_chain {F : Finset Cand} (hne : F.Nonempty)
    (hchain : ∀ a ∈ F, ∀ b ∈ F, T.Finer a b ∨ T.Finer b a) (hF : T.Feasible F) :
    ∃ d ∈ F, T.Feasible {d} := by
  obtain ⟨d, hdF, hd⟩ := T.exists_finest F hne hchain
  refine ⟨d, hdF, ?_⟩
  intro p hp
  obtain ⟨e, heF, hpe⟩ := T.mem_Covered.mp (hF hp)
  exact T.mem_Covered.mpr ⟨d, Finset.mem_singleton_self d, T.Cov_mono (hd e heF) hpe⟩

/-! ### Totality: the solver may not refuse

A finite task is decidable -- whether a hypothesis fits the teachers can always be checked -- so a
refusal is a defect of the theory, never a property of the task.  The first version refused twice:
when the frozen family could not separate some pair, and when a block of the answer had never been
revealed.  Both are repaired here, and neither repair is a heuristic.

* **Completeness of the family.**  A family containing one distinction that separates every pair of
  sites makes every task separable.  Such a distinction always exists -- naming the site does it --
  so `Separable` is never a reason to refuse; it is only ever a statement about a family too poor,
  and the fix is to enrich the family rather than to decline the task.
* **Totality of the read-out.**  The answer is a **total** function of the site: where a block was
  revealed it is that block's target, and where it was not it is a declared fallback.  What the
  theory then guarantees is exact: the answer is correct at every site whose block was revealed.
-/

omit [DecidableEq Site] [Fintype Cand] [DecidableEq Cand] in
/-- **No task is unseparable for a family that can tell the sites apart.** -/
theorem separable_of_injective {d : Cand} (hd : Function.Injective (T.dist d)) : T.Separable := by
  intro p hp
  refine ⟨d, T.mem_Cov.mpr ⟨T.mem_Need.mp hp, ?_⟩⟩
  intro hdist
  exact (T.mem_Need.mp hp) (congrArg T.target (hd hdist))

open Classical in
/-- The answer at a site: the target of a revealed site in the same block, or the fallback.

Total by construction -- there is no case in which it declines -- and deterministic, since what it
returns where a block was revealed does not depend on which revealed site is picked: that is
exactly what admissibility says. -/
noncomputable def answerFrom (F : Finset Cand) (Rev : Finset Site) (fallback : ℕ) (i : Site) : ℕ :=
  if h : ∃ j ∈ Rev, (T.agree F).r i j then T.target h.choose else fallback

omit [Fintype Site] [DecidableEq Site] [Fintype Cand] [DecidableEq Cand] in
/-- **Exactness is local, and the global hypothesis was too strong.**  The answer at a site depends only
on that site's block, so only *that* block need be free of two different answers -- admissibility for the
whole task is more than is needed.  Found by measurement: on the sample every solved task had an impure
block somewhere, and `answerFrom_eq_target` could not account for it while this can. -/
theorem answerFrom_eq_target_of_pure {F : Finset Cand} {Rev : Finset Site} {fallback : ℕ} {i : Site}
    (hpure : ∀ j : Site, (T.agree F).r i j → T.target i = T.target j)
    (h : ∃ j ∈ Rev, (T.agree F).r i j) :
    T.answerFrom F Rev fallback i = T.target i := by
  rw [answerFrom, dif_pos h]
  exact (hpure _ h.choose_spec.2).symm

omit [Fintype Cand] [DecidableEq Cand] in
/-- **What totality costs, and what it keeps.**  On an admissible family the answer is correct at
every site whose block some revealed site shares; elsewhere it is the declared fallback and the
theory says nothing about it, which is the honest statement rather than a refusal. -/
theorem answerFrom_eq_target {F : Finset Cand} {Rev : Finset Site} {fallback : ℕ} {i : Site}
    (hF : T.Feasible F) (h : ∃ j ∈ Rev, (T.agree F).r i j) :
    T.answerFrom F Rev fallback i = T.target i := by
  have hle := (T.feasible_iff_le_ker F).mp hF
  rw [answerFrom]
  rw [dif_pos h]
  exact (hle h.choose_spec.2).symm

omit [Fintype Cand] [DecidableEq Cand] in
/-- A revealed site is always answered, and answered with its own target. -/
theorem answerFrom_eq_target_of_mem {F : Finset Cand} {Rev : Finset Site} {fallback : ℕ}
    {i : Site} (hF : T.Feasible F) (hi : i ∈ Rev) :
    T.answerFrom F Rev fallback i = T.target i :=
  T.answerFrom_eq_target hF ⟨i, hi, (T.agree F).refl i⟩

omit [Fintype Cand] [DecidableEq Cand] in
/-- **The solver is exact whenever the teachers left no block unshown.**

The precondition is the whole content: it says what the teachers must have covered, and
`unvouched_blocks_le` says a coarser quotient makes it easier to meet.  Nothing else is needed and
nothing else is promised. -/
theorem exact_of_all_revealed {F : Finset Cand} {Rev : Finset Site} {fallback : ℕ}
    (hF : T.Feasible F) (hall : ∀ i : Site, ∃ j ∈ Rev, (T.agree F).r i j) :
    ∀ i : Site, T.answerFrom F Rev fallback i = T.target i :=
  fun i => T.answerFrom_eq_target hF (hall i)


/-! ### The limit of the guarantee

Everything above is about the pairs the target **reveals**.  A solver only ever sees a subset of the
source, so the honest question is whether covering what was revealed says anything about what was
not.  It does not, and that is exhibited rather than argued: the claim is refuted by a three-site
task below.

This is the corpus's P5 in this setting -- certification is meaningful only relative to an explicitly
frozen hypothesis class -- and it is the reason the algorithmic guarantee and any claim of transfer
must stay separate statements. -/

/-- The pairs the target separates **among the sites that were revealed**. -/
def NeedOn (O : Finset Site) : Finset (Site × Site) :=
  T.Need.filter fun p => p.1 ∈ O ∧ p.2 ∈ O

/-- Admissible on what was revealed. -/
def FeasibleOn (O : Finset Site) (F : Finset Cand) : Prop := T.NeedOn O ⊆ T.Covered F

omit [Fintype Cand] [DecidableEq Cand] in
theorem feasible_imp_feasibleOn (O : Finset Site) (F : Finset Cand) (h : T.Feasible F) :
    T.FeasibleOn O F :=
  fun _ hp => h (Finset.mem_of_mem_filter _ hp)

end Task

instance decidableRepresentative [Fintype Site] [DecidableEq Site] [Fintype Cand]
    [DecidableEq Cand] (T : Task Site Cand) (S : Finset (Site × Site)) :
    Decidable (T.Representative S) :=
  inferInstanceAs (Decidable (∀ p ∈ T.Need, ∃ q ∈ S, T.sig q = T.sig p))

instance decidableSeparable [Fintype Site] [DecidableEq Site] [Fintype Cand] [DecidableEq Cand]
    (T : Task Site Cand) : Decidable T.Separable :=
  inferInstanceAs (Decidable (∀ p ∈ T.Need, ∃ d : Cand, p ∈ T.Cov d))

instance decidableFeasible [Fintype Site] [DecidableEq Site] [DecidableEq Cand]
    (T : Task Site Cand) (F : Finset Cand) : Decidable (T.Feasible F) :=
  inferInstanceAs (Decidable (T.Need ⊆ T.Covered F))

instance decidableFeasibleOn [Fintype Site] [DecidableEq Site] [DecidableEq Cand]
    (T : Task Site Cand) (O : Finset Site) (F : Finset Cand) : Decidable (T.FeasibleOn O F) :=
  inferInstanceAs (Decidable (T.NeedOn O ⊆ T.Covered F))

/-- A three-site witness: one distinction separates the revealed pair and glues an unrevealed one. -/
def gapTask : Task (Fin 3) (Fin 1) where
  dist := fun _ i => if i = 0 then 0 else 1
  target := fun i => (i : ℕ)

/-- **Covering what was revealed does not cover what was not.**  The family is admissible on the
revealed sites and inadmissible on the source, so no guarantee proved above transfers by itself. -/
theorem gap_feasibleOn_not_feasible :
    gapTask.FeasibleOn {0, 1} Finset.univ ∧ ¬ gapTask.Feasible Finset.univ := by
  constructor
  · decide
  · decide

/-! ### A language from a dissimilarity: the chain is automatic, the objective is the margin

The previous section priced enrichment: distinctions that are not comparable break the chain and the
ordered-hitting problem returns.  So the question for anything that *produces* distinctions -- a
parameterised family, a network -- is how to produce a chain.

The answer needs no design.  Let the thing produce a **dissimilarity**: a scale attached to each
pair, with no assumption at all -- not symmetry, not a triangle inequality.  Its language is the
filtration by scale: at scale `t`, glue whatever a chain of steps no larger than `t` links.  Then

* the family is a chain **for free**, by monotonicity of the equivalence closure;
* admissibility at scale `t` holds **exactly** when every pair the target separates is farther apart
  than `t`;

so the two-sided objective of `card_targets_le_nblocks` reads off directly: push the differently
targeted apart (that is admissibility, and it is the margin), pull the alike together (that is
coarseness, and it is what is left to minimise).  This is a contrastive objective, arrived at as a
theorem rather than borrowed as a technique.
-/

section Scale

universe w'

variable {Site : Type w'}

/-- The language of a dissimilarity: at scale `t`, glue whatever steps of size at most `t` link. -/
def scale (w : Site → Site → ℕ) (t : ℕ) : Setoid Site :=
  Relation.EqvGen.setoid (fun x y => w x y ≤ t)

/-- **The chain is automatic.**  A larger scale glues at least as much, so a single scalar parameter
gives a totally ordered language and never an unordered bag. -/
theorem scale_mono (w : Site → Site → ℕ) {t t' : ℕ} (h : t ≤ t') : scale w t ≤ scale w t' := by
  intro x y hxy
  exact Relation.EqvGen.mono (fun a b hab => le_trans hab h) hxy

/-- **Admissibility at a scale is exactly a margin condition.**  The language at scale `t` refines
the target precisely when the dissimilarity keeps every pair the target separates farther apart than
`t` -- one direction is the guarantee, the other says the condition is not merely sufficient. -/
theorem scale_le_ker_iff (w : Site → Site → ℕ) (f : Site → ℕ) (t : ℕ) :
    scale w t ≤ Setoid.ker f ↔ ∀ x y : Site, f x ≠ f y → t < w x y := by
  constructor
  · intro hle x y hne
    by_contra hcon
    exact hne (hle (Relation.EqvGen.rel x y (by omega)))
  · intro hmar x y hxy
    show f x = f y
    induction hxy with
    | rel a b hab =>
        by_contra hne
        exact absurd (hmar a b hne) (by omega)
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ hab hbc => exact hab.trans hbc

/-- **The coarsest admissible scale is found by one comparison, not by a search.**  Below the margin
every scale is admissible and above it none is, so the optimum of the chain is its top admissible
element and the scan of `exists_single_of_chain` has length one here. -/
theorem scale_le_ker_of_lt (w : Site → Site → ℕ) (f : Site → ℕ) {t m : ℕ}
    (hm : ∀ x y : Site, f x ≠ f y → m ≤ w x y) (ht : t < m) :
    scale w t ≤ Setoid.ker f :=
  (scale_le_ker_iff w f t).mpr fun x y hne => lt_of_lt_of_le ht (hm x y hne)

end Scale

/-! ### Encoding the target: what "coarsest recoverable" is, and what it is not

The last thing left outside the theory is how the answer is said.  A site is asked to become
something; the solver must be able to produce it from the role it reads off the quotient **and from
what the site itself shows** -- never from the answer, which it does not have.  That is the whole
condition, and it turns out to be a condition on kernels.

The section also corrects a claim made earlier in this file's own planning: that the principle
"coarsest recoverable" **determines** the encoding.  It does not.  There are cases with two
recoverable encodings and no recoverable encoding coarser than both, so the maxima are genuinely
several and a choice among them is a real branching, not a lapse of discipline.
-/

section Encoding

universe w₁ w₂ w₃ w₄

variable {Site : Type w₁} {O : Type w₂} {V : Type w₃}
variable (obs : Site → O) (ans : Site → V)

/-- An encoding of the answer is **recoverable** when the answer can be read back from the role and
what the site shows -- and from nothing else. -/
def Recoverable {R : Type w₄} (f : Site → R) : Prop :=
  ∃ dec : R → O → V, ∀ i : Site, dec (f i) (obs i) = ans i

/-- **Recoverability is a condition on kernels.**  It says exactly: sites that carry the same role
and show the same thing are asked for the same thing. -/
theorem recoverable_iff [Nonempty V] {R : Type w₄} (f : Site → R) :
    Recoverable obs ans f ↔ ∀ i j : Site, f i = f j → obs i = obs j → ans i = ans j := by
  classical
  constructor
  · rintro ⟨dec, hdec⟩ i j hf ho
    rw [← hdec i, ← hdec j, hf, ho]
  · intro h
    refine ⟨fun r o => if hx : ∃ i : Site, f i = r ∧ obs i = o then ans hx.choose
      else Classical.arbitrary V, fun i => ?_⟩
    have hx : ∃ k : Site, f k = f i ∧ obs k = obs i := ⟨i, rfl, rfl⟩
    dsimp only
    rw [dif_pos hx]
    exact h hx.choose i hx.choose_spec.1 hx.choose_spec.2

/-- **Naming the answer always works**, so the set of recoverable encodings is never empty and the
solver is never left without one. -/
theorem recoverable_ans : Recoverable obs ans ans := ⟨fun v _ => v, fun _ => rfl⟩

end Encoding

/-! #### The maxima are several: a three-site witness -/

/-- What each site shows: two of them show the same thing. -/
def demoObs : Fin 3 → Fin 2 := fun i => if i = 1 then 1 else 0

/-- What each site is asked to become: the two that show the same thing differ. -/
def demoAns : Fin 3 → Fin 2 := fun i => if i = 2 then 1 else 0

/-- One recoverable encoding: it glues the first two. -/
def demoF : Fin 3 → Fin 2 := fun i => if i = 2 then 1 else 0

/-- Another: it glues the last two. -/
def demoG : Fin 3 → Fin 2 := fun i => if i = 0 then 0 else 1

theorem demoF_recoverable : Recoverable demoObs demoAns demoF :=
  (recoverable_iff demoObs demoAns demoF).mpr (by decide)

theorem demoG_recoverable : Recoverable demoObs demoAns demoG :=
  (recoverable_iff demoObs demoAns demoG).mpr (by decide)

/-- **There is no recoverable encoding coarser than both.**  So "the coarsest recoverable encoding"
does not exist in general: the maxima are incomparable, and choosing among them is a genuine finite
branching that the theory must acknowledge rather than legislate away. -/
theorem no_common_coarsening :
    ¬ ∃ (R : Type) (h : Fin 3 → R), Recoverable demoObs demoAns h ∧
        (∀ i j, demoF i = demoF j → h i = h j) ∧ (∀ i j, demoG i = demoG j → h i = h j) := by
  rintro ⟨R, h, hrec, hF, hG⟩
  obtain ⟨dec, hdec⟩ := hrec
  have h01 : h 0 = h 1 := hF 0 1 (by decide)
  have h12 : h 1 = h 2 := hG 1 2 (by decide)
  have h02 : h 0 = h 2 := h01.trans h12
  have hobs : demoObs 0 = demoObs 2 := by decide
  have : demoAns 0 = demoAns 2 := by
    rw [← hdec 0, ← hdec 2, h02, hobs]
  exact absurd this (by decide)

/-! ## Identification: the family may depend on the query's input, the class must be declared

`gap_feasibleOn_not_feasible` is a countermodel to every **fixed** family: separating the revealed pairs
never implies separating the rest.  `witness_discrete_of_sigCovered` closes the obvious escape -- the one
checkable form of the transfer hypothesis certifies exactly the runs that transfer nothing.  So no
condition on a fixed family can be both checkable and non-empty, and the object has to change.

What changes it is that `Feasible` asks about a target the solver does not have, while the honest
question is about **every target the revealed part leaves possible**.  Declare that set: a finite class
`H` of candidate targets, frozen before the answer is seen.  Then

* which hypotheses survive (`Consistent`) mentions the target **only on the revealed sites**;
* which pairs must be separated (`NeedH`) is therefore **computable**;
* and `Identifies` -- the family separates all of them -- is **decidable** (`decidableIdentifies`).

That is the whole difference from `Feasible`, which is not checkable: the quantifier moved from an
unknown target to a declared class.  The guarantee is then unconditional apart from one assumption that
cannot be removed and is stated in every theorem below: **the truth is in `H`**.  That is P5 of the
corpus -- certification is meaningful only relative to an explicitly frozen hypothesis class.

**Where the query's input enters, and the rule it must obey.**  `H` may be built from the sources: the
teachers' pairs and the query's **input**, never the query's output.  The theorems here are agnostic
about how `H` is built, which is exactly where a DSL would be smuggled in: a hand-authored `H` is a menu
and falls under the no-DSL rule of `CLAUDE.md`.  `H` has to be produced by a construction -- the
generator's job, and the reason the generator exists.

**The price, and it is a theorem, not a caveat.**  `consistent_unique_of_exact` says that identification
plus full coverage forces the revealed data to leave exactly **one** surviving hypothesis, and
`not_covered_of_ambiguous` says a site about which two survivors disagree cannot be covered at all.  So
the guarantee of a complete answer is available precisely when `H` is narrow enough for the teachers to
single out one member.  The work is not a better covering; it is a narrower class.
-/

section Identification

-- The `unusedSectionVars` linter and `omit` disagree here: the linter reports the four instances as
-- unused while `omit` refuses them as referenced (`Finset.univ` and `DecidableEq` inside the
-- definitions these statements mention).  Silenced locally rather than left as noise, and locally so
-- that a genuinely unused variable elsewhere still shows.
set_option linter.unusedSectionVars false

variable [Fintype Site] [DecidableEq Site] [Fintype Cand] [DecidableEq Cand]

namespace Task

variable (T : Task Site Cand) (O : Finset Site) (H : Finset (Site → ℕ))

/-- The declared hypotheses the revealed part does not refute.  Mentions the target only on `O`. -/
def Consistent : Finset (Site → ℕ) := H.filter fun h => ∀ i ∈ O, h i = T.target i

omit [Fintype Cand] [DecidableEq Cand] in
theorem mem_Consistent {h : Site → ℕ} :
    h ∈ T.Consistent O H ↔ h ∈ H ∧ ∀ i ∈ O, h i = T.target i := by
  simp [Consistent, Finset.mem_filter]

/-- Two sites every surviving hypothesis assigns alike: nothing the revealed part allows tells them
apart, so nothing has to. -/
def AllAgree (x y : Site) : Prop := ∀ h ∈ T.Consistent O H, h x = h y

instance decidableAllAgree (T : Task Site Cand) (O : Finset Site) (H : Finset (Site → ℕ))
    (x y : Site) : Decidable (T.AllAgree O H x y) :=
  inferInstanceAs (Decidable (∀ h ∈ T.Consistent O H, h x = h y))

/-- **What has to be separated, computably.**  The counterpart of `Need`, with the unknown target
replaced by the declared class. -/
def NeedH : Finset (Site × Site) :=
  Finset.univ.filter fun p => ¬ T.AllAgree O H p.1 p.2

omit [Fintype Cand] [DecidableEq Cand] in
@[simp] theorem mem_NeedH {p : Site × Site} :
    p ∈ T.NeedH O H ↔ ¬ T.AllAgree O H p.1 p.2 := by
  simp [NeedH, Finset.mem_filter]

/-- The pairs a candidate separates, unconditionally -- `Cov` is filtered by `Need`, and `Need` is
exactly what is unavailable. -/
def Sep (d : Cand) : Finset (Site × Site) :=
  Finset.univ.filter fun p => T.dist d p.1 ≠ T.dist d p.2

/-- What a chosen subfamily separates, unconditionally. -/
def SepBy (F : Finset Cand) : Finset (Site × Site) := F.biUnion T.Sep

omit [Fintype Cand] [DecidableEq Cand] in
@[simp] theorem mem_SepBy {p : Site × Site} {F : Finset Cand} :
    p ∈ T.SepBy F ↔ ∃ d ∈ F, T.dist d p.1 ≠ T.dist d p.2 := by
  simp [SepBy, Sep, Finset.mem_biUnion, Finset.mem_filter]

/-- **Identification.**  The chosen family separates every pair two surviving hypotheses disagree on.
Unlike `Feasible`, this is decidable from the revealed data and `H` alone. -/
def Identifies (F : Finset Cand) : Prop := T.NeedH O H ⊆ T.SepBy F

omit [Fintype Cand] [DecidableEq Cand] in
/-- The truth is among the survivors, provided it was declared. -/
theorem target_mem_Consistent (htrue : T.target ∈ H) : T.target ∈ T.Consistent O H :=
  (T.mem_Consistent O H).mpr ⟨htrue, fun _ _ => rfl⟩

omit [Fintype Cand] [DecidableEq Cand] in
/-- **Identification is exactly "every survivor is constant on the blocks".** -/
theorem identifies_iff (F : Finset Cand) :
    T.Identifies O H F ↔ ∀ h ∈ T.Consistent O H, T.agree F ≤ Setoid.ker h := by
  constructor
  · intro hid h hh x y hxy
    show h x = h y
    by_contra hne
    have hp : (x, y) ∈ T.NeedH O H := (T.mem_NeedH O H).mpr fun hall => hne (hall h hh)
    obtain ⟨d, hdF, hd⟩ := T.mem_SepBy.mp (hid hp)
    exact hd (hxy d hdF)
  · intro hall p hp
    rw [T.mem_NeedH O H] at hp
    by_contra hno
    refine hp fun h hh => hall h hh fun d hdF => ?_
    by_contra hd
    exact hno (T.mem_SepBy.mpr ⟨d, hdF, hd⟩)

omit [Fintype Cand] [DecidableEq Cand] in
/-- **The bridge a fixed family cannot have.**  With the truth declared, a **checkable** condition gives
admissibility for the truth itself -- which `FeasibleOn` never gave. -/
theorem feasible_of_identifies {F : Finset Cand} (htrue : T.target ∈ H)
    (hid : T.Identifies O H F) : T.Feasible F :=
  (T.feasible_iff_le_ker F).mpr
    ((T.identifies_iff O H F).mp hid T.target (T.target_mem_Consistent O H htrue))

omit [Fintype Cand] [DecidableEq Cand] in
/-- **The guarantee that was asked for: exact at every site.**  The truth declared, the family
identifying, every block meeting the revealed set -- then the total read-out is the target everywhere,
the unrevealed sites included. -/
theorem exact_of_identifies {F : Finset Cand} {fallback : ℕ} (htrue : T.target ∈ H)
    (hid : T.Identifies O H F) (hcov : ∀ i : Site, ∃ j ∈ O, (T.agree F).r i j) (i : Site) :
    T.answerFrom F O fallback i = T.target i :=
  T.answerFrom_eq_target (T.feasible_of_identifies O H htrue hid) (hcov i)

omit [Fintype Cand] [DecidableEq Cand] in
/-- **The price, per site.**  A site about which two survivors disagree cannot share a block with any
revealed site: the guarantee is not merely silent there, it is provably unavailable. -/
theorem not_covered_of_ambiguous {F : Finset Cand} (hid : T.Identifies O H F) {i : Site}
    {h₁ h₂ : Site → ℕ} (hh₁ : h₁ ∈ T.Consistent O H) (hh₂ : h₂ ∈ T.Consistent O H)
    (hne : h₁ i ≠ h₂ i) : ¬ ∃ j ∈ O, (T.agree F).r i j := by
  rintro ⟨j, hjO, hij⟩
  have e₁ : h₁ i = h₁ j := (T.identifies_iff O H F).mp hid h₁ hh₁ hij
  have e₂ : h₂ i = h₂ j := (T.identifies_iff O H F).mp hid h₂ hh₂ hij
  have t₁ : h₁ j = T.target j := ((T.mem_Consistent O H).mp hh₁).2 j hjO
  have t₂ : h₂ j = T.target j := ((T.mem_Consistent O H).mp hh₂).2 j hjO
  exact hne (by rw [e₁, e₂, t₁, t₂])

omit [Fintype Cand] [DecidableEq Cand] in
/-- **The price, in full.**  A complete guarantee is available exactly when the revealed part leaves one
survivor: identification plus full coverage forces any two survivors to be the same function.  So the
work is not a better covering but a narrower class, and that is a theorem rather than an opinion. -/
theorem consistent_unique_of_exact {F : Finset Cand} (hid : T.Identifies O H F)
    (hcov : ∀ i : Site, ∃ j ∈ O, (T.agree F).r i j)
    {h₁ h₂ : Site → ℕ} (hh₁ : h₁ ∈ T.Consistent O H) (hh₂ : h₂ ∈ T.Consistent O H) : h₁ = h₂ := by
  funext i
  obtain ⟨j, hjO, hij⟩ := hcov i
  have e₁ : h₁ i = h₁ j := (T.identifies_iff O H F).mp hid h₁ hh₁ hij
  have e₂ : h₂ i = h₂ j := (T.identifies_iff O H F).mp hid h₂ hh₂ hij
  have t₁ : h₁ j = T.target j := ((T.mem_Consistent O H).mp hh₁).2 j hjO
  have t₂ : h₂ j = T.target j := ((T.mem_Consistent O H).mp hh₂).2 j hjO
  rw [e₁, e₂, t₁, t₂]

/-! #### Identification is a covering problem, so the polynomial bounds apply to it

`NeedH` is the complement of `AllAgree`, and `AllAgree` is an equivalence -- an intersection of kernels.
So there is a target whose `Need` is exactly `NeedH`: number the blocks.  With that, identification *is*
admissibility for a derived task, and the greedy of this file, its `log` bound and its cost bound apply
to it unchanged.  Nothing new is assumed; a definition is supplied so the existing theorems reach.
-/

theorem allAgree_refl (x : Site) : T.AllAgree O H x x := fun _ _ => rfl

theorem allAgree_symm {x y : Site} (h : T.AllAgree O H x y) : T.AllAgree O H y x :=
  fun g hg => (h g hg).symm

theorem allAgree_trans {x y z : Site} (h₁ : T.AllAgree O H x y) (h₂ : T.AllAgree O H y z) :
    T.AllAgree O H x z := fun g hg => (h₁ g hg).trans (h₂ g hg)

/-- The block of a site: the sites no survivor tells it apart from. -/
def blockH (i : Site) : Finset Site := Finset.univ.filter fun j => T.AllAgree O H i j

theorem blockH_eq_iff {x y : Site} : T.blockH O H x = T.blockH O H y ↔ T.AllAgree O H x y := by
  constructor
  · intro h
    have hy : y ∈ T.blockH O H y := by
      simp only [blockH, Finset.mem_filter, Finset.mem_univ, true_and]
      exact T.allAgree_refl O H y
    rw [← h] at hy
    simpa only [blockH, Finset.mem_filter, Finset.mem_univ, true_and] using hy
  · intro h
    refine Finset.ext fun k => ?_
    simp only [blockH, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hk => T.allAgree_trans O H (T.allAgree_symm O H h) hk,
           fun hk => T.allAgree_trans O H h hk⟩

/-- The blocks, numbered: a target whose kernel is `AllAgree`. -/
noncomputable def hypTarget (i : Site) : ℕ :=
  (Fintype.equivFin (Finset Site)) (T.blockH O H i)

theorem hypTarget_eq_iff {x y : Site} :
    T.hypTarget O H x = T.hypTarget O H y ↔ T.AllAgree O H x y := by
  refine Iff.trans ?_ (T.blockH_eq_iff O H)
  exact ⟨fun h => (Fintype.equivFin (Finset Site)).injective (Fin.val_injective h),
         fun h => by simp only [hypTarget, h]⟩

/-- **The derived task.**  Same distinctions; the target separates exactly what the survivors disagree
on.  Identification for `T` is admissibility for this. -/
noncomputable def hyp : Task Site Cand := { dist := T.dist, target := T.hypTarget O H }

theorem hyp_need : (T.hyp O H).Need = T.NeedH O H := by
  refine Finset.ext fun p => ?_
  rw [mem_Need, T.mem_NeedH O H]
  exact not_congr (T.hypTarget_eq_iff O H)

theorem identifies_iff_feasible_hyp (F : Finset Cand) :
    T.Identifies O H F ↔ (T.hyp O H).Feasible F := by
  constructor
  · intro hid p hp
    have hp' : p ∈ T.NeedH O H := by rwa [T.hyp_need O H] at hp
    obtain ⟨d, hdF, hd⟩ := T.mem_SepBy.mp (hid hp')
    exact (T.hyp O H).mem_Covered.mpr
      ⟨d, hdF, (T.hyp O H).mem_Cov.mpr ⟨(T.hyp O H).mem_Need.mp hp, hd⟩⟩
  · intro hF p hp
    have hp' : p ∈ (T.hyp O H).Need := by rwa [T.hyp_need O H]
    obtain ⟨d, hdF, hd⟩ := (T.hyp O H).mem_Covered.mp (hF hp')
    exact T.mem_SepBy.mpr ⟨d, hdF, ((T.hyp O H).mem_Cov.mp hd).2⟩

/-- **Identification in polynomial time, with a logarithmic size bound.**  The greedy run on the derived
task returns an identifying family within a `log₂ |NeedH| + 1` factor of any identifying family, and
`solve_cost` bounds the work -- the same guarantees as for covering, because it is the same problem. -/
theorem identify_log {F₀ : Finset Cand} (hid : T.Identifies O H F₀) (hk : 1 ≤ F₀.card)
    (cands : List Cand) (hall : ∀ d : Cand, d ∈ cands) :
    T.Identifies O H
        (greedy (T.hyp O H) cands
          ((Nat.log 2 (T.NeedH O H).card + 1) * F₀.card) (T.NeedH O H) ∅) ∧
      (greedy (T.hyp O H) cands
          ((Nat.log 2 (T.NeedH O H).card + 1) * F₀.card) (T.NeedH O H) ∅).card
        ≤ (Nat.log 2 (T.NeedH O H).card + 1) * F₀.card := by
  have hF : (T.hyp O H).Feasible F₀ := (T.identifies_iff_feasible_hyp O H F₀).mp hid
  have h := (T.hyp O H).solve_log hF hk cands hall
  rw [T.hyp_need O H] at h
  exact ⟨(T.identifies_iff_feasible_hyp O H _).mpr h.1, h.2⟩

/-- **Checkable.**  This is the whole point: `Feasible` is not decidable for a solver, because it
mentions the target where the target is unknown; `Identifies` is. -/
instance decidableIdentifies (T : Task Site Cand) (O : Finset Site) (H : Finset (Site → ℕ))
    (F : Finset Cand) : Decidable (T.Identifies O H F) :=
  inferInstanceAs (Decidable (T.NeedH O H ⊆ T.SepBy F))

end Task

end Identification

/-! ### The generator: where `H` comes from, and the limit on any way of producing it

M-S15 leaves `H` given.  That is exactly the place a menu would be smuggled in, so the class has to be
**produced** -- and produced from the sources alone: the candidate distinctions (a function of every
site's input, the query's included) and the target **only where it was revealed**.  Three properties say
what a producer must have, and they are stated as properties of a function rather than of a program, so
no construction is privileged:

* `SourceOnly` -- two tasks with the same distinctions and the same revealed target get the same class.
  This is the formal content of "from the sources only, never from the query's answer".
* `Sound` -- the truth is in the class.  Unremovable (P5), and it is what `target ∈ H` assumed.
* `SharpAt` -- the revealed part leaves at most one survivor.  `consistent_unique_of_exact` proved this
  is forced by a complete guarantee, so it is not an extra wish but the same demand restated.

And then the limit, which is the point of this section: **no producer has all three.**  A source-only
generator cannot distinguish two worlds that agree on what was revealed, so soundness makes it keep both
and sharpness makes it keep one.  Hence a guarantee is available only relative to a **declared family of
admissible worlds** -- `SoundOn` below -- and the empirical question is not whether the solver is clever
but how often the truth lies in the family it declares.  That is P5 turned into something measurable.
-/

section Generator

-- As in `section Identification`: the linter reports these as unused while `omit` refuses them as
-- referenced inside the definitions the statements mention.  Silenced locally, not globally.
set_option linter.unusedSectionVars false

variable [Fintype Site] [DecidableEq Site] [Fintype Cand] [DecidableEq Cand]

/-- A producer of hypothesis classes. -/
abbrev Generator (Site : Type u) (Cand : Type v) := Task Site Cand → Finset (Site → ℕ)

/-- **From the sources only.**  The class may depend on the distinctions and on the target where it was
revealed, and on nothing else -- in particular not on the query's answer. -/
def SourceOnly (O : Finset Site) (G : Generator Site Cand) : Prop :=
  ∀ T₁ T₂ : Task Site Cand, T₁.dist = T₂.dist →
    (∀ i ∈ O, T₁.target i = T₂.target i) → G T₁ = G T₂

/-- **The truth is declared.**  This is the assumption `target ∈ H` of M-S15, as a property of the
producer rather than of one run. -/
def Sound (G : Generator Site Cand) : Prop := ∀ T : Task Site Cand, T.target ∈ G T

/-- **The truth is declared, for the worlds the theory admits.**  The weakening that survives the limit
theorem below: soundness is claimed only where the target belongs to a declared family. -/
def SoundOn (W : Finset (Site → ℕ)) (G : Generator Site Cand) : Prop :=
  ∀ T : Task Site Cand, T.target ∈ W → T.target ∈ G T

/-- **The revealed part leaves one survivor.**  Forced by `consistent_unique_of_exact` whenever a
complete guarantee is wanted. -/
def SharpAt (O : Finset Site) (G : Generator Site Cand) : Prop :=
  ∀ T : Task Site Cand, ∀ h₁ ∈ T.Consistent O (G T), ∀ h₂ ∈ T.Consistent O (G T), h₁ = h₂

namespace Task

variable (T : Task Site Cand) (O : Finset Site) (H : Finset (Site → ℕ))

/-- **When the class is sharp the covering is unnecessary.**  One survivor and the truth declared, and
the answer is that survivor -- no family, no quotient, no read-out.  So the whole covering apparatus is a
*way of sharpening*, never a second source of guarantee. -/
theorem target_eq_of_sharp (htrue : T.target ∈ H) {h : Site → ℕ} (hh : h ∈ T.Consistent O H)
    (huniq : ∀ g ∈ T.Consistent O H, ∀ g' ∈ T.Consistent O H, g = g') : T.target = h :=
  huniq T.target (T.target_mem_Consistent O H htrue) h hh

/-- Identification only gets easier as the family grows, so the sharp question is the **smallest**
identifying family -- a covering problem over `NeedH`, which is what the greedy of this file solves. -/
theorem identifies_mono {F F' : Finset Cand} (hFF : F ⊆ F') (hid : T.Identifies O H F) :
    T.Identifies O H F' := by
  intro p hp
  obtain ⟨d, hdF, hd⟩ := T.mem_SepBy.mp (hid hp)
  exact T.mem_SepBy.mpr ⟨d, hFF hdF, hd⟩

end Task

/-- **The limit on any producer of classes.**  A source-only generator that is sound and sharp forces
the revealed part to determine the target outright: two worlds agreeing on `O` and offering the same
distinctions must be the same world.  So `Sound` cannot be had together with `SharpAt` unless there was
nothing to learn. -/
theorem target_eq_of_sourceOnly {O : Finset Site} {G : Generator Site Cand}
    (hso : SourceOnly O G) (hsound : Sound G) (hsharp : SharpAt O G)
    (T₁ T₂ : Task Site Cand) (hd : T₁.dist = T₂.dist)
    (hO : ∀ i ∈ O, T₁.target i = T₂.target i) : T₁.target = T₂.target := by
  have hH : G T₁ = G T₂ := hso T₁ T₂ hd hO
  have h1 : T₁.target ∈ T₁.Consistent O (G T₁) :=
    T₁.target_mem_Consistent O (G T₁) (hsound T₁)
  have h2 : T₂.target ∈ T₁.Consistent O (G T₁) := by
    refine (T₁.mem_Consistent O (G T₁)).mpr ⟨?_, fun i hi => (hO i hi).symm⟩
    rw [hH]; exact hsound T₂
  exact hsharp T₁ T₁.target h1 T₂.target h2


/-- **The guarantee that survives the limit.**  For a producer sound on a **declared** family of worlds,
every task whose target belongs to that family is answered exactly -- the family is the one assumption,
and it is explicit rather than hidden in a threshold. -/
theorem exact_of_soundOn {W : Finset (Site → ℕ)} {G : Generator Site Cand} {O : Finset Site}
    {F : Finset Cand} {fallback : ℕ} (hs : SoundOn W G) (T : Task Site Cand) (hW : T.target ∈ W)
    (hid : T.Identifies O (G T) F) (hcov : ∀ i : Site, ∃ j ∈ O, (T.agree F).r i j) (i : Site) :
    T.answerFrom F O fallback i = T.target i :=
  T.exact_of_identifies O (G T) (hs T hW) hid hcov i


/-! #### Declaring a family, and why a partition cannot be the declaration

`no_sound_sharp_generator` leaves no choice: a family of admissible worlds has to be declared.  What
makes a declaration good is one property -- **the revealed sites tell its members apart** -- and then the
answer is read off the declaration with no covering at all.  That is the whole of M-S17's positive half.

Its negative half is about the declaration this project has been using without writing down.  The class
the runtime behaves as if it declared is "every world constant on the blocks of the chosen family", and
`exists_rival_of_unrevealed_block` shows such a class is **never** separated once one block holds no
revealed site: a rival world agrees everywhere it was checked and differs on that block.  So for a
partition-declared class the two demands pull the partition in opposite directions -- coarser to have
every block revealed, finer to keep the truth constant on blocks -- and the measurement of M-S16 is that
tension in numbers: 73 of 102 tasks fail soundness, 85 fail sharpness, 63 fail both.
-/

/-- Declaring a family: the producer that offers it whatever the task.  Source-only for the strongest
possible reason -- it does not look at the task at all. -/
def constGen (W : Finset (Site → ℕ)) : Generator Site Cand := fun _ => W

/-- **A family the revealed sites tell apart.**  Two admissible worlds that agree wherever the teachers
spoke are the same world. -/
def SeparatedBy (O : Finset Site) (W : Finset (Site → ℕ)) : Prop :=
  ∀ h₁ ∈ W, ∀ h₂ ∈ W, (∀ i ∈ O, h₁ i = h₂ i) → h₁ = h₂

theorem sourceOnly_constGen (O : Finset Site) (W : Finset (Site → ℕ)) :
    SourceOnly (Cand := Cand) O (constGen W) := fun _ _ _ _ => rfl

theorem soundOn_constGen (W : Finset (Site → ℕ)) :
    SoundOn (Cand := Cand) W (constGen W) := fun _ h => h

/-- Separation is exactly sharpness for a declared family. -/
theorem sharpAt_constGen {O : Finset Site} {W : Finset (Site → ℕ)} (hsep : SeparatedBy O W) :
    SharpAt (Cand := Cand) O (constGen W) := by
  intro T h₁ hh₁ h₂ hh₂
  obtain ⟨hw₁, ho₁⟩ := (T.mem_Consistent O W).mp hh₁
  obtain ⟨hw₂, ho₂⟩ := (T.mem_Consistent O W).mp hh₂
  exact hsep h₁ hw₁ h₂ hw₂ fun i hi => (ho₁ i hi).trans (ho₂ i hi).symm

/-- **The positive half of M-S17.**  A declared family that the revealed sites tell apart, and that
contains the truth, **determines** the answer: the surviving world *is* the truth.  No family of
candidates, no quotient, no read-out -- the covering apparatus is only a way of computing this. -/
theorem target_eq_of_separated {O : Finset Site} {W : Finset (Site → ℕ)}
    (hsep : SeparatedBy O W) (T : Task Site Cand) (hW : T.target ∈ W)
    {h : Site → ℕ} (hh : h ∈ T.Consistent O W) : T.target = h := by
  obtain ⟨hw, ho⟩ := (T.mem_Consistent O W).mp hh
  exact hsep T.target hW h hw fun i hi => (ho i hi).symm

namespace Task

variable (T : Task Site Cand) (O : Finset Site)

/-- **The negative half of M-S17: a partition cannot be the declaration.**  Suppose the truth is
constant on the blocks of `F` -- soundness for the class a partition declares -- and some site's block
holds no revealed site.  Then a **rival** world is equally constant on the blocks and agrees with the
truth everywhere the teachers spoke, so the class is not separated and the guarantee is unavailable.
Coarser blocks are needed for sharpness and finer ones for soundness, and that is the tension measured
in M-S16 rather than a shortcoming of one implementation. -/
theorem exists_rival_of_unrevealed_block {F : Finset Cand}
    (hF : T.agree F ≤ Setoid.ker T.target) {i : Site} (hi : ∀ j ∈ O, ¬ (T.agree F).r i j) :
    ∃ g : Site → ℕ, T.agree F ≤ Setoid.ker g ∧ (∀ j ∈ O, g j = T.target j) ∧ g ≠ T.target := by
  classical
  refine ⟨fun j => T.target j + (if (T.agree F).r i j then 1 else 0), ?_, ?_, ?_⟩
  · intro x y hxy
    have ht : T.target x = T.target y := hF hxy
    have hiff : (T.agree F).r i x ↔ (T.agree F).r i y :=
      ⟨fun h => (T.agree F).trans' h hxy, fun h => (T.agree F).trans' h ((T.agree F).symm' hxy)⟩
    show T.target x + (if (T.agree F).r i x then 1 else 0)
        = T.target y + (if (T.agree F).r i y then 1 else 0)
    rw [ht]
    by_cases hx : (T.agree F).r i x
    · rw [if_pos hx, if_pos (hiff.mp hx)]
    · rw [if_neg hx, if_neg fun hy => hx (hiff.mpr hy)]
  · intro j hj
    show T.target j + (if (T.agree F).r i j then 1 else 0) = T.target j
    rw [if_neg (hi j hj), Nat.add_zero]
  · intro heq
    have hc := congrFun heq i
    simp only [if_pos ((T.agree F).refl' i)] at hc
    omega

end Task
end Generator

/-! ### The theory is not empty, and the countermodel now speaks before the answer is seen -/

/-- The three sites of `gapTask` with a target its one candidate can carry. -/
def idTask : Task (Fin 3) (Fin 1) where
  dist := fun _ i => if i = 1 then 1 else 0
  target := fun i => if i = 1 then 1 else 0

/-- **Non-empty, with genuine transfer.**  Two of the three sites are revealed, the family identifies,
and the third -- unrevealed -- shares a block with a revealed one. -/
theorem idTask_identifies_and_covers :
    idTask.Identifies {0, 1} {idTask.target} Finset.univ ∧
      ∀ i : Fin 3, ∃ j ∈ ({0, 1} : Finset (Fin 3)), (idTask.agree Finset.univ).r i j := by
  refine ⟨by decide, fun i => ?_⟩
  have h : ∀ i : Fin 3, ∃ j ∈ ({0, 1} : Finset (Fin 3)),
      ∀ d ∈ (Finset.univ : Finset (Fin 1)), idTask.dist d i = idTask.dist d j := by decide
  obtain ⟨j, hj, hd⟩ := h i
  exact ⟨j, hj, fun d hdF => hd d hdF⟩

/-- So the answer is the target at **every** site, the unrevealed one included. -/
theorem idTask_exact (fallback : ℕ) (i : Fin 3) :
    idTask.answerFrom Finset.univ {0, 1} fallback i = idTask.target i :=
  idTask.exact_of_identifies {0, 1} {idTask.target} (Finset.mem_singleton_self _)
    idTask_identifies_and_covers.1 idTask_identifies_and_covers.2 i

/-- A world offering the same distinctions as `idTask` and agreeing with it wherever `idTask` reveals
anything, yet a different world. -/
def altTask : Task (Fin 3) (Fin 1) where
  dist := fun _ i => if i = 1 then 1 else 0
  target := fun i => if i = 1 then 1 else if i = 2 then 2 else 0

/-- **No producer of hypothesis classes has all three properties.**  Source-only, sound for every world,
sharp on the revealed part -- the three are jointly unsatisfiable, and one pair of three-site worlds
witnesses it.  So a guarantee is available only relative to a declared family of admissible worlds
(`exact_of_soundOn`), and how often the truth lies in that family is a measurement, not a theorem. -/
theorem no_sound_sharp_generator (G : Generator (Fin 3) (Fin 1)) :
    ¬ (SourceOnly {0, 1} G ∧ Sound G ∧ SharpAt {0, 1} G) := by
  rintro ⟨hso, hsound, hsharp⟩
  have h := target_eq_of_sourceOnly hso hsound hsharp idTask altTask rfl (by decide)
  exact absurd (congrFun h 2) (by decide)

/-- **And the countermodel is now diagnosed in advance.**  On `gapTask` the same family, with the truth
declared, **fails to identify**, and that failure is decidable -- so a solver can see it before it
answers, where `gap_feasibleOn_not_feasible` could only be seen afterwards. -/
theorem gapTask_not_identifies :
    ¬ gapTask.Identifies {0, 1} {gapTask.target} Finset.univ := by decide

/-! ## The observation order, after SRT Observer Theory O3/O5

The scale of `section Scale` indexes cuts by a **number**, and SRT's frozen Observer Theory says in so
many words why that cannot be the object.  O3 §4 identifies the observation poset with `EqRel(X)ᵒᵖ` --
the index of an observer is its **kernel**, and the information order is reverse kernel inclusion -- and
O3 §10 shows the poset of scalar-valued observers has no top: two incomparable coordinates have no
scalar refinement, so "maximal information ≠ canonical scalar observer".  `no_adequate_scale_glues`
below is that statement in this setting, and it is the reason M-S17 measured the chain's ceiling at 4 of
102 tasks.

O3 §9 then supplies what the theory here was missing.  Relative to a declared relation `E` an observer
is *extensional* when `E ⊆ K_o` and *conservative* when `K_o ⊆ E`, and Theorem 9.3 says both hold
exactly when `K_o = E`.  Taking `E` to be the question's kernel -- a **choice**, and O3 warns against
identifying resolution with observation merely because both are relations on the same carrier -- the two
conditions read on the revealed part as: no block holds two revealed sites the question separates
(conservativity, already present as `FeasibleOn`), and no two revealed sites the question calls the same
sit in different blocks (**extensionality**, which nothing here has ever demanded).  Extensionality
mentions the target only where it was revealed, so unlike `Feasible` it is decidable for a solver.

Measured before being formalised, on 102 tasks: enforcing it takes extensionality violations from a
median 122 to 0 and the quotient from a median 180 blocks to 48, at no cost -- and moves the *unrevealed*
side not at all (median 42 query blocks without a revealed site, before and after).  So it is the
coarsest-quotient principle finally enforced where it can be checked, and it is **not** a cure for dead
provenance; SRT separates those two diseases and so does the measurement.

O5 names the rest: `Feasible` is *adequacy* (sensitivity to the question's declared distinctions), and
O5-T3 makes the finest available observer the ceiling -- `exists_feasible_iff` below.  What O5 calls
`AdeqDebt = R_Q ∩ K_{E_P}` is then the honest diagnosis when the ceiling fails: not a worse cut but an
inadequate presentation, and explicitly not permission to add target-fitted primitives.
-/

section ObserverOrder

-- As in the earlier sections: the linter reports these as unused where `omit` refuses them.
set_option linter.unusedSectionVars false

variable [Fintype Site] [DecidableEq Site] [Fintype Cand] [DecidableEq Cand]

namespace Task

variable (T : Task Site Cand) (O : Finset Site)

/-- **Extensionality on the revealed part** (SRT O3 §9, `E ⊆ K_o`, with `E` the question's kernel).
Two revealed sites the question calls the same must share a block.  Checkable: the target is mentioned
only on `O`. -/
def Extensional (F : Finset Cand) : Prop :=
  ∀ x ∈ O, ∀ y ∈ O, T.target x = T.target y → (T.agree F).r x y

/-- **SRT O3 Theorem 9.3 in this setting.**  Extensional and conservative together say exactly that the
observer's kernel **equals** the question's kernel on the revealed part -- neither finer nor coarser.
That is `S/ker η` of the corpus, pinned from both sides by data the solver has. -/
theorem extensional_and_feasibleOn_iff (F : Finset Cand) :
    (T.Extensional O F ∧ T.FeasibleOn O F) ↔
      ∀ x ∈ O, ∀ y ∈ O, ((T.agree F).r x y ↔ T.target x = T.target y) := by
  constructor
  · rintro ⟨hext, hcons⟩ x hx y hy
    refine ⟨fun hxy => ?_, hext x hx y hy⟩
    by_contra hne
    have hp : (x, y) ∈ T.NeedOn O :=
      Finset.mem_filter.mpr ⟨T.mem_Need.mpr hne, hx, hy⟩
    obtain ⟨d, hdF, hd⟩ := T.mem_Covered.mp (hcons hp)
    exact (T.mem_Cov.mp hd).2 (hxy d hdF)
  · intro h
    refine ⟨fun x hx y hy he => (h x hx y hy).mpr he, fun p hp => ?_⟩
    obtain ⟨hne, hx, hy⟩ := Finset.mem_filter.mp hp
    by_contra hno
    refine T.mem_Need.mp hne ((h p.1 hx p.2 hy).mp fun d hdF => ?_)
    by_contra hd
    exact hno (T.mem_Covered.mpr ⟨d, hdF, T.mem_Cov.mpr ⟨T.mem_Need.mp hne, hd⟩⟩)

/-- **SRT O5-T3, the adequacy ceiling.**  The finest available observer decides whether any is adequate,
so a failure is a statement about the declared family and not about the search. -/
theorem feasible_univ_of_feasible {F : Finset Cand} (h : T.Feasible F) :
    T.Feasible (Finset.univ : Finset Cand) := by
  intro p hp
  obtain ⟨d, _, hd⟩ := T.mem_Covered.mp (h hp)
  exact T.mem_Covered.mpr ⟨d, Finset.mem_univ d, hd⟩

theorem exists_feasible_iff :
    (∃ F : Finset Cand, T.Feasible F) ↔ T.Feasible (Finset.univ : Finset Cand) :=
  ⟨fun ⟨_, h⟩ => T.feasible_univ_of_feasible h, fun h => ⟨Finset.univ, h⟩⟩


/-- **SRT O5 Definition 6.2, the presentation adequacy debt.**  The pairs the question separates that even
the **finest available** observer glues.  It mentions no search: it is a property of the declared family. -/
def AdeqDebt : Finset (Site × Site) :=
  T.Need.filter fun p => ∀ d ∈ (Finset.univ : Finset Cand), T.dist d p.1 = T.dist d p.2

theorem mem_AdeqDebt {p : Site × Site} :
    p ∈ T.AdeqDebt ↔ p ∈ T.Need ∧ (T.agree (Finset.univ : Finset Cand)).r p.1 p.2 := by
  simp only [AdeqDebt, Finset.mem_filter, Task.agree_apply]

theorem feasible_univ_iff_debt_empty :
    T.Feasible (Finset.univ : Finset Cand) ↔ T.AdeqDebt = ∅ := by
  constructor
  · intro h
    refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
    obtain ⟨hne, hagr⟩ := T.mem_AdeqDebt.mp hp
    obtain ⟨d, _, hd⟩ := T.mem_Covered.mp (h hne)
    exact (T.mem_Cov.mp hd).2 (hagr d (Finset.mem_univ d))
  · intro h p hp
    by_contra hno
    have : p ∈ T.AdeqDebt := T.mem_AdeqDebt.mpr ⟨hp, fun d _ => by
      by_contra hd
      exact hno (T.mem_Covered.mpr ⟨d, Finset.mem_univ d, T.mem_Cov.mpr ⟨T.mem_Need.mp hp, hd⟩⟩)⟩
    rw [h] at this
    exact absurd this (Finset.notMem_empty p)

/-- **A non-empty debt is a verdict on the presentation, not on the search.**  No family of candidates is
adequate, so no cut, no objective and no ordering can help: the declared distinctions have to change --
and O5 adds, in so many words, that this is not permission to add target-fitted primitives. -/
theorem not_exists_feasible_of_debt (h : T.AdeqDebt.Nonempty) :
    ¬ ∃ F : Finset Cand, T.Feasible F := by
  intro hex
  have := (T.feasible_univ_iff_debt_empty).mp (T.exists_feasible_iff.mp hex)
  exact absurd this (Finset.nonempty_iff_ne_empty.mp h)

/-! ### What the code actually chooses, and the debt as the obstruction to meaning

`Feasible` quantifies over **subfamilies** `F ⊆ Cand`, but the cuts this project computes are not of that
form: they are closures of witnessed merges over carriers, i.e. equivalences at least as coarse as the
envelope `agree univ`.  Every `agree F` is such an equivalence, so the subfamily form is the special case
and the theorems below are the general one -- which is what the code needs and what it never had.

At that generality two statements become available and both are short.  The coarsest adequate equivalence
is the question's own kernel, `Setoid.ker target`, which is the corpus's `S/ker η`: **meaning**.  And it is
realisable exactly when the presentation adequacy debt is empty.  So a non-empty debt does not merely
block one search -- it says meaning itself lies outside the reach of the declared distinctions.
-/

/-- What the declared family can realise: any equivalence at least as coarse as the envelope.  A solver
may coarsen what the language sees; it cannot invent a distinction the language does not make. -/
def Realisable (K : Setoid Site) : Prop := T.agree (Finset.univ : Finset Cand) ≤ K

theorem realisable_agree (F : Finset Cand) : T.Realisable (T.agree F) := by
  intro x y h d _
  exact h d (Finset.mem_univ d)

/-- **The debt obstructs every realisable equivalence, not merely every subfamily.** -/
theorem debt_empty_of_realisable_adequate {K : Setoid Site}
    (hR : T.Realisable K) (hA : K ≤ Setoid.ker T.target) : T.AdeqDebt = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨hne, hagr⟩ := T.mem_AdeqDebt.mp hp
  exact T.mem_Need.mp hne (hA (hR hagr))

/-- **Meaning is reachable exactly when the debt is empty.**  `Setoid.ker target` is the coarsest adequate
equivalence -- the corpus's `S/ker η` -- and the debt is precisely the obstruction to realising it. -/
theorem realisable_ker_iff_debt_empty :
    T.Realisable (Setoid.ker T.target) ↔ T.AdeqDebt = ∅ := by
  refine ⟨fun hR => T.debt_empty_of_realisable_adequate hR le_rfl, fun h x y hxy => ?_⟩
  show T.target x = T.target y
  by_contra hne
  have : (x, y) ∈ T.AdeqDebt := T.mem_AdeqDebt.mpr ⟨T.mem_Need.mpr hne, hxy⟩
  rw [h] at this
  exact absurd this (Finset.notMem_empty _)

open Classical in
/-- The total read-out of an arbitrary equivalence, not only of a subfamily's. -/
noncomputable def answerAt (K : Setoid Site) (Rev : Finset Site) (fallback : ℕ) (i : Site) : ℕ :=
  if h : ∃ j ∈ Rev, K.r i j then T.target h.choose else fallback

theorem answerAt_eq_target {K : Setoid Site} {Rev : Finset Site} {fallback : ℕ} {i : Site}
    (hA : K ≤ Setoid.ker T.target) (h : ∃ j ∈ Rev, K.r i j) :
    T.answerAt K Rev fallback i = T.target i := by
  rw [answerAt, dif_pos h]
  exact (hA h.choose_spec.2).symm

/-- **The guarantee, stated on the presentation and the teachers alone.**  If the debt is empty -- so the
language can realise meaning -- and every site's answer was exhibited at some revealed site, then reading
off the question's own quotient is exact everywhere.  Neither condition mentions a search, an objective or
an ordering: what remains is to *find* that quotient, which is what identification is for. -/
theorem exact_of_debt_empty_and_live {Rev : Finset Site} {fallback : ℕ}
    (hlive : ∀ i : Site, ∃ j ∈ Rev, T.target i = T.target j) (i : Site) :
    T.answerAt (Setoid.ker T.target) Rev fallback i = T.target i :=
  T.answerAt_eq_target le_rfl (hlive i)

/-! ### What the revealed data can and cannot decide: the envelope settles it

Before building any generator, the question has to be asked exactly, or heuristics fill the gap.  It is
this: when is there an equivalence that is realisable (`agree univ ≤ K`), equal to the question's kernel on
the revealed part (`extensional_and_feasibleOn_iff`) and **live** -- every site sharing its block with a
revealed one -- and when such an equivalence exists, is it unique?

The answer is complete and it removes the search rather than improving it.

* If the envelope already refines the question (`AdeqDebt = ∅`) and every site is envelope-equivalent to a
  revealed one, then reading the answer off **the envelope itself** is exact everywhere
  (`exact_of_envelope`).  No subfamily, no cut, no ordering and no objective takes part: the data decide.
* If even one site is envelope-equivalent to no revealed site, then a second world agrees with everything
  revealed, is equally admissible, and answers that site differently (`underdetermined_of_novel`).  So the
  revealed data **cannot** decide it -- not by a better search, since there is nothing to search: every
  choice is consistent with everything known.

Both conditions are checkable before answering: the debt reads the target only where it was revealed, and
novelty reads the inputs alone.  That is the specification a generator must be held to, and it is two
numbers rather than a family of rules.
-/

/-- **When the data decide, the envelope is the answer.**  Nothing finer is needed and nothing coarser is
admissible: the whole covering apparatus is a way of *computing* this, never a second source of truth. -/
theorem exact_of_envelope {O : Finset Site} {fallback : ℕ}
    (hadq : T.agree (Finset.univ : Finset Cand) ≤ Setoid.ker T.target)
    (hlive : ∀ i : Site, ∃ j ∈ O, (T.agree (Finset.univ : Finset Cand)).r i j) (i : Site) :
    T.answerAt (T.agree (Finset.univ : Finset Cand)) O fallback i = T.target i :=
  T.answerAt_eq_target hadq (hlive i)

/-- **At a novel site the data permit *any* answer.**  Not merely "some rival exists": for every value at
all there is a world that agrees with everything revealed, is equally refined by the envelope, and answers
the novel site by that value.  So admissibility constrains the answer there **not at all**, and every
constraint a solver can have comes from the language -- from which sites share a carrier -- and never from
the conditions on the quotient.  That is why no cut, order, objective or search moved the count: they all
choose among worlds the data cannot tell apart. -/
theorem exists_world_of_any_value {O : Finset Site} {q : Site} (v : ℕ)
    (hadq : T.agree (Finset.univ : Finset Cand) ≤ Setoid.ker T.target)
    (hq : ∀ j ∈ O, ¬ (T.agree (Finset.univ : Finset Cand)).r q j) :
    ∃ g : Site → ℕ,
      (∀ i ∈ O, g i = T.target i) ∧
      (T.agree (Finset.univ : Finset Cand) ≤ Setoid.ker g) ∧
      g q = v := by
  classical
  refine ⟨fun i => if (T.agree (Finset.univ : Finset Cand)).r q i then v else T.target i,
    ?_, ?_, ?_⟩
  · intro i hi
    show (if _ then _ else _) = _
    rw [if_neg (hq i hi)]
  · intro x y hxy
    show (if _ then _ else _) = (if _ then _ else _)
    have hiff : (T.agree (Finset.univ : Finset Cand)).r q x
        ↔ (T.agree (Finset.univ : Finset Cand)).r q y :=
      ⟨fun h => (T.agree _).trans' h hxy, fun h => (T.agree _).trans' h ((T.agree _).symm' hxy)⟩
    by_cases hx : (T.agree (Finset.univ : Finset Cand)).r q x
    · rw [if_pos hx, if_pos (hiff.mp hx)]
    · rw [if_neg hx, if_neg fun hy => hx (hiff.mpr hy)]
      exact hadq hxy
  · show (if _ then _ else _) = v
    rw [if_pos ((T.agree (Finset.univ : Finset Cand)).refl' q)]

/-- **And when one site is novel, nothing decides it.**  A site the envelope separates from every revealed
site admits a rival world: same distinctions, same revealed answers, equally refined by the envelope, and a
different answer there.  So underdetermination at such a site is a theorem about the data, not a failure of
the solver -- and the only repair is a language in which the site is not novel. -/
theorem underdetermined_of_novel {O : Finset Site} {q : Site}
    (hadq : T.agree (Finset.univ : Finset Cand) ≤ Setoid.ker T.target)
    (hq : ∀ j ∈ O, ¬ (T.agree (Finset.univ : Finset Cand)).r q j) :
    ∃ g : Site → ℕ,
      (∀ i ∈ O, g i = T.target i) ∧
      (T.agree (Finset.univ : Finset Cand) ≤ Setoid.ker g) ∧
      g q ≠ T.target q := by
  classical
  refine ⟨fun i => T.target i + (if (T.agree (Finset.univ : Finset Cand)).r q i then 1 else 0),
    ?_, ?_, ?_⟩
  · intro i hi
    show T.target i + _ = T.target i
    rw [if_neg (hq i hi), Nat.add_zero]
  · intro x y hxy
    show T.target x + _ = T.target y + _
    have ht : T.target x = T.target y := hadq hxy
    have hiff : (T.agree (Finset.univ : Finset Cand)).r q x
        ↔ (T.agree (Finset.univ : Finset Cand)).r q y :=
      ⟨fun h => (T.agree _).trans' h hxy, fun h => (T.agree _).trans' h ((T.agree _).symm' hxy)⟩
    rw [ht]
    by_cases hx : (T.agree (Finset.univ : Finset Cand)).r q x
    · rw [if_pos hx, if_pos (hiff.mp hx)]
    · rw [if_neg hx, if_neg fun hy => hx (hiff.mpr hy)]
  · show T.target q + _ ≠ T.target q
    rw [if_pos ((T.agree (Finset.univ : Finset Cand)).refl' q)]
    omega

/-! ### The missing parameter: an order on worlds

Everything above is conditional on a declared class of worlds, and the class was never instantiated.  With
the trivial instantiation -- every function constant on envelope classes -- `exists_world_of_any_value`
makes the answer undetermined at 96.6 % of query sites, while the same runtime answers 75.5 % of them
correctly and a person solves the tasks from the same examples.  Both cannot be right about one notion of
"determined", so the notion is too weak: the theory models what the solver knows and not that the world is
**regular**.

Measured, the regularity is enormous and the teachers exhibit it: 80.3 % of query sites keep their own
class, and a median 84.5 % of revealed sites do.  The data are used here only as *constraints* -- equality
on the revealed part -- and never as evidence about which worlds are likely; all `4 ^ 126` assignments
satisfy the constraints and a vanishing fraction match the exhibited statistics.

So what is missing is not a larger family of distinctions but a **preference among the worlds the data
cannot tell apart**.  Declaring it is not a heuristic: minimality is already the corpus's definition of
meaning (the coarsest quotient), already the tie-break this project uses, and it is declared before any
evaluation, which is the order O5 §10 requires.  Below, `cost` is that declaration and everything is stated
relative to it; with a constant `cost` the statements degenerate to the vacuous ones, which is exactly the
state the theory was in.
-/

/-- The cheapest worlds of a declared class, under a declared cost. -/
def Cheapest (cost : (Site → ℕ) → ℕ) (W : Finset (Site → ℕ)) : Finset (Site → ℕ) :=
  W.filter fun h => ∀ g ∈ W, cost h ≤ cost g

theorem mem_Cheapest {cost : (Site → ℕ) → ℕ} {W : Finset (Site → ℕ)} {h : Site → ℕ} :
    h ∈ Cheapest cost W ↔ h ∈ W ∧ ∀ g ∈ W, cost h ≤ cost g := by
  simp [Cheapest, Finset.mem_filter]

/-- A non-empty class has a cheapest member: the declaration is always usable. -/
theorem cheapest_nonempty (cost : (Site → ℕ) → ℕ) {W : Finset (Site → ℕ)} (hW : W.Nonempty) :
    (Cheapest cost W).Nonempty := by
  classical
  obtain ⟨h, hh, hmin⟩ := Finset.exists_min_image W cost hW
  exact ⟨h, mem_Cheapest.mpr ⟨hh, hmin⟩⟩

/-- **Determinacy becomes agreement among the *minimisers*, not among all admissible worlds.**  That is
the whole content of the completion: the admissible class is astronomically large and agrees on almost
nothing, while its cheapest members can agree everywhere.  With a constant cost the two coincide and the
statement degenerates to the vacuous one. -/
theorem cheapest_eq_target {cost : (Site → ℕ) → ℕ} {W : Finset (Site → ℕ)} {O : Finset Site}
    (hmin : T.target ∈ Cheapest cost (T.Consistent O W))
    {h : Site → ℕ} (hh : h ∈ Cheapest cost (T.Consistent O W)) {i : Site}
    (hagree : ∀ g₁ ∈ Cheapest cost (T.Consistent O W),
              ∀ g₂ ∈ Cheapest cost (T.Consistent O W), g₁ i = g₂ i) :
    h i = T.target i :=
  hagree h hh T.target hmin

/-- And when the cheapest world is unique, every site is determined -- no agreement hypothesis is needed
and no search remains. -/
theorem cheapest_unique_eq_target {cost : (Site → ℕ) → ℕ} {W : Finset (Site → ℕ)} {O : Finset Site}
    (hmin : T.target ∈ Cheapest cost (T.Consistent O W))
    (huniq : ∀ g₁ ∈ Cheapest cost (T.Consistent O W),
             ∀ g₂ ∈ Cheapest cost (T.Consistent O W), g₁ = g₂)
    {h : Site → ℕ} (hh : h ∈ Cheapest cost (T.Consistent O W)) : h = T.target :=
  huniq h hh T.target hmin

end Task

/-- Checkable, which `Feasible` is not. -/
instance decidableExtensional (T : Task Site Cand) (O : Finset Site) (F : Finset Cand) :
    Decidable (T.Extensional O F) :=
  decidable_of_iff
    (∀ x ∈ O, ∀ y ∈ O, T.target x = T.target y → ∀ d ∈ F, T.dist d x = T.dist d y)
    (by simp only [Task.Extensional, Task.agree_apply])

end ObserverOrder

/-! ### SRT O3 §10 here: an adequate scale glues nothing

Two incomparable coordinates over four sites, the question being one of them.  Every scale of the
Hamming dissimilarity is either the discrete relation or glues everything, so the coordinate observer --
which is adequate and does glue -- is realised by **no** scale.  Hence for this task any adequate scale
is discrete: the scalar index skips the informative middle, which is what O3 §10 asserts abstractly and
what `runs/scale/chain.py` measured as a median gap of 5 on a chain of median length 16.
-/

/-- Four sites read as two bits; the two coordinates are the candidates and the question is the first. -/
def bitTask : Task (Fin 4) (Fin 2) where
  dist := fun d i => if d = 0 then (i : ℕ) / 2 else (i : ℕ) % 2
  target := fun i => (i : ℕ) / 2

/-- The Hamming dissimilarity of the two coordinates. -/
def hammingBits (x y : Fin 4) : ℕ :=
  (if (x : ℕ) / 2 = (y : ℕ) / 2 then 0 else 1) + (if (x : ℕ) % 2 = (y : ℕ) % 2 then 0 else 1)

theorem no_adequate_scale_glues (t : ℕ)
    (hadq : scale hammingBits t ≤ Setoid.ker bitTask.target) :
    ∀ x y : Fin 4, (scale hammingBits t).r x y → x = y := by
  have hzero : t = 0 := by
    by_contra hne
    have ht : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr hne
    have hstep : hammingBits 0 2 ≤ t := by
      have : hammingBits 0 2 = 1 := by decide
      omega
    have := hadq (Relation.EqvGen.rel (0 : Fin 4) 2 hstep)
    have hne2 : bitTask.target 0 ≠ bitTask.target 2 := by decide
    exact hne2 this
  subst hzero
  intro x y hxy
  induction hxy with
  | rel a b hab =>
      have h0 : hammingBits a b = 0 := Nat.le_zero.mp hab
      exact (by decide : ∀ u v : Fin 4, hammingBits u v = 0 → u = v) a b h0
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ hab hbc => exact hab.trans hbc

/-! ## Complete solution: what an equivariant family guarantees

Everything above asks whether the state being asked about shares a class with a state that was shown, and
`exists_world_of_any_value` then says that where it does not, nothing is determined.  That is the arithmetic
of a **lookup**: a table has no entry for a key it has not seen.

The corpus's object is not a table.  `S_op = S / ⋂ ker O` with every observer a **homomorphism**, so what
the continuation does is visible in the observation itself, and the observation is a total function of the
state.  Then the answer at a state that was never shown is determined all the same -- not because the state
was seen but because its **observation** was.

Two conditions, and both are statements about the family rather than about the sample:

* **equivariance** -- the observer commutes with the continuation, `O (rho x) = f (O x)`;
* **faithfulness** -- the joint observation tells states apart.

With the first alone the *observation* of the answer is determined everywhere; with both, the answer itself.
And the honest limit is the corpus's own: a family that is not faithful reconstructs `S_op` and not `S`, so
the answer is determined only up to what the family can see -- which is a statement about the language and
not about which states happened to be shown.
-/

section Solution

variable {St V : Type*} {ι : Type*}

/-- The observer commutes with the continuation: what the continuation does is visible in the observation
alone.  Checkable where the continuation was shown, and a statement about the family everywhere. -/
def Equivariant (O : St → V) (rho : St → St) (f : V → V) : Prop :=
  ∀ x, O (rho x) = f (O x)

/-- The family tells states apart -- the corpus's joint faithfulness. -/
def Faithful (O : ι → St → V) : Prop := ∀ x y : St, (∀ i, O i x = O i y) → x = y

/-- **The observation of the answer is determined by the observation of the state**, for every state,
shown or not.  Nothing here asks whether `x` was seen. -/
theorem obs_of_answer (O : ι → St → V) (rho : St → St) (f : ι → V → V)
    (h : ∀ i, Equivariant (O i) rho (f i)) (x : St) (i : ι) :
    O i (rho x) = f i (O i x) := h i x

/-- **Determined up to what the family sees.**  Equivariance alone already gives this much: two states the
family cannot tell apart have answers the family cannot tell apart.  This is the corpus's `S_op` and not
`S`. -/
theorem answer_indist (O : ι → St → V) (rho : St → St) (f : ι → V → V)
    (heq : ∀ i, Equivariant (O i) rho (f i)) {x y : St} (h : ∀ i, O i x = O i y) (i : ι) :
    O i (rho x) = O i (rho y) := by
  rw [heq i x, heq i y, h i]

/-- **Complete solution.**  With an equivariant **faithful** family the continuation is a function of the
observation: states observed alike have the same answer, and no state needs to have been shown.  This is the
guarantee the lookup reading could not give, and its hypotheses are about the family, not about the sample. -/
theorem answer_determined (O : ι → St → V) (rho : St → St) (f : ι → V → V)
    (heq : ∀ i, Equivariant (O i) rho (f i)) (hf : Faithful O) {x y : St}
    (h : ∀ i, O i x = O i y) : rho x = rho y :=
  hf _ _ fun i => answer_indist O rho f heq h i

/-- **Faithfulness cannot be dropped.**  Equivariance alone leaves the answer undetermined: a family that
sees nothing is equivariant for the identity and yet says nothing about any continuation. -/
theorem faithful_needed :
    ∃ (O : Unit → Bool → Unit) (rho : Bool → Bool) (f : Unit → Unit → Unit),
      (∀ i, Equivariant (O i) rho (f i)) ∧ (∀ i, O i true = O i false) ∧ rho true ≠ rho false :=
  ⟨fun _ _ => (), fun b => b, fun _ _ => (), fun _ _ => rfl, fun _ => rfl, by decide⟩


/-! ### A family complete for a task, and what it guarantees

The guarantee wanted is not "these tasks are solved" but "every asked state is answered, and correctly".
Three conditions on the family give it, and none of them mentions which states happened to be shown except
the third, which says the family is coarse enough that nothing asked is new **to the family**.

* `equivariant` -- the observation of the continuation is a function of the observation;
* `determines` -- the observation determines the continuation itself;
* `known` -- every asked state is observed as some shown state is.

`complete_answer` then says: the answer at an asked state **is** the answer at a shown one.  So the answer is
not merely determined in principle, it is available, for every asked state, with nothing left to search.

What is checkable and what is not is stated rather than blurred.  `equivariant` and `known` are decided on
the shown part alone.  `determines` is checkable only there, and off it is the corpus's P5 -- an assumption
about the family, which is a thing one builds, and not about the sample, which is a thing one is given.
`unambiguous_answer` isolates exactly how much follows without it: the answer is unique, though its
correctness still rests on the assumption.
-/

/-- A family complete for a task: equivariant, determining, and coarse enough that nothing asked is new. -/
structure CompleteFor (O : St → V) (rho : St → St) (f : V → V)
    (shown asked : St → Prop) : Prop where
  equivariant : ∀ x, O (rho x) = f (O x)
  determines : ∀ x y, O x = O y → rho x = rho y
  known : ∀ x, asked x → ∃ y, shown y ∧ O x = O y

/-- **The guarantee.**  With a complete family every asked state's answer is the answer of a shown state --
available, not merely determined. -/
theorem complete_answer {O : St → V} {rho : St → St} {f : V → V} {shown asked : St → Prop}
    (h : CompleteFor O rho f shown asked) {x : St} (hx : asked x) :
    ∃ y, shown y ∧ rho x = rho y := by
  obtain ⟨y, hy, ho⟩ := h.known x hx
  exact ⟨y, hy, h.determines x y ho⟩

/-- **What holds without the unverifiable half.**  Drop `determines` off the shown part and the answer is
still **unambiguous**: any two shown states observed like the asked one agree.  Correctness needs the
assumption; uniqueness does not. -/
theorem unambiguous_answer {O : St → V} {rho : St → St} {shown : St → Prop}
    (hdet : ∀ x y, shown x → shown y → O x = O y → rho x = rho y)
    {x y z : St} (hy : shown y) (hz : shown z) (hoy : O x = O y) (hoz : O x = O z) :
    rho y = rho z := hdet y z hy hz (hoy.symm.trans hoz)


/-- **Exactly when the guarantee is achievable.**  A family complete for the task exists **if and only if**
every asked state's answer already occurs among the shown answers.  One direction is `complete_answer`; the
other takes the continuation itself as the observer, which is equivariant and determining for free.

So the guarantee is not a matter of cleverness: it is available precisely when the presented part exhibits
every answer the asked part needs, and unavailable otherwise whatever is built.  That is a condition on the
**task**, and it is the exact form of "the examples suffice". -/
theorem completeFor_iff (rho : St → St) (shown asked : St → Prop) :
    (∃ (O : St → St) (f : St → St), CompleteFor O rho f shown asked)
      ↔ (∀ x, asked x → ∃ y, shown y ∧ rho x = rho y) := by
  constructor
  · rintro ⟨O, f, h⟩ x hx
    exact complete_answer h hx
  · intro h
    refine ⟨rho, rho, ⟨fun _ => rfl, fun x y hxy => hxy, ?_⟩⟩
    intro x hx
    obtain ⟨y, hy, hr⟩ := h x hx
    exact ⟨y, hy, hr⟩


/-! ### The guarantee without any condition on the sample

`CompleteFor` demands `known`: every asked state must be observed as some shown state is.  That demand is
what makes the answer a **copy**, and it is the last remnant of the lookup reading -- a table has to find the
key.  What follows does not remove that demand; it **moves** it, from the states to the world's operation.  In `AlgObsFamily` each observed world carries its **own signature**
and the observer is a homomorphism into it, so `f` is not a table fitted over states: it is an operation of
the observed world, total and known.  Then the observation of the answer is **computed** wherever the
observation is defined, which is everywhere.

What the examples are for, on this reading, is to settle the world's operation -- one small object per
world -- and not to be searched for a matching key.  That is why abundance helps: many states, few
observation values.

So the guarantee below carries no condition on which states were shown -- but it is not thereby a
guarantee.  `homomorphic_exists` shows the hypotheses are satisfiable for **any** continuation (take the
identity observer and the continuation itself as the world's operation), so all the content sits in "the
world's operation is known", and for an opaque `V` that is the old `known` again, a table keyed by an
observed value.  What the reduction is worth is therefore decided later, in `Generated`: if the observed
world is **generated** and the operation is a homomorphism, knowing it on the generators is knowing it
everywhere, and the condition on the sample drops from "every asked state" to "every generator".
-/

/-- An observed world with its own operation -- the corpus's `sigW`, kept to the one symbol used here. -/
structure ObservedWorld (V : Type*) where
  op : V → V

/-- The observer is a homomorphism: the continuation is the world's own operation, seen through it. -/
def Homomorphic (O : St → V) (rho : St → St) (W : ObservedWorld V) : Prop :=
  ∀ x, O (rho x) = W.op (O x)

/-- **Complete solution, with no condition on the sample.**  With a faithful homomorphic family the answer
at **every** state is reconstructed by solving the observation equations: the state whose observations are
the world's operations applied to the observations of `x` **is** the answer at `x`.  Nothing here asks
whether `x`, or anything observed like it, was ever shown. -/
theorem answer_reconstructed (O : ι → St → V) (rho : St → St) (W : ι → ObservedWorld V)
    (hh : ∀ i, Homomorphic (O i) rho (W i)) (hf : Faithful O) {x z : St}
    (h : ∀ i, O i z = (W i).op (O i x)) : z = rho x :=
  hf _ _ fun i => (h i).trans (hh i x).symm

/-- And the answer always satisfies those equations, so the reconstruction is not vacuous: the system has
the answer as a solution, and by `answer_reconstructed` no other. -/
theorem answer_satisfies (O : ι → St → V) (rho : St → St) (W : ι → ObservedWorld V)
    (hh : ∀ i, Homomorphic (O i) rho (W i)) (x : St) (i : ι) :
    O i (rho x) = (W i).op (O i x) := hh i x

/-- **Where the remaining assumption lives.**  A homomorphic family exists for any continuation -- take the
identity observer and the continuation as the world's operation -- so the content is never existence but
whether the world's operation is **known**.  The examples settle it; the theorem says they need settle only
that, and nothing about which states were shown. -/
theorem homomorphic_exists (rho : St → St) :
    ∃ (O : St → St) (W : ObservedWorld St), Homomorphic O rho W :=
  ⟨id, ⟨rho⟩, fun _ => rfl⟩


/-! ### The observed world generated (v0.22 signature)

The reduction above is worth exactly as much as the phrase "the world's operation is known".  Here it is
given content by the corpus's own signature `Sig` -- `oplus, ominus, rho` -- rather than by a new one.

An observed world is **generated** when every value is reached from a set of generators by `oplus`.  The
continuation, seen through a homomorphic observer, is then an **additive** map, and an additive map is
determined by its values on the generators.  So the sample must pin the operation on the generators only,
and that is a statement about a small set of values, not about the asked states.

This is the first place where the guarantee stops being conditional on coverage of what is asked.  What it
costs is stated as plainly: additivity is a hypothesis about the **task** -- it says the answer decomposes
along `oplus` -- and it can fail.  The theorem does not hide that; it isolates it as one named hypothesis
that a run can check.
-/

/-- The part of an observed world reached from `gen` by the signature's binary operation. -/
inductive Span {V : Type*} (W : Sig V) (gen : V → Prop) : V → Prop
  | base {v} : gen v → Span W gen v
  | oplus {a b} : Span W gen a → Span W gen b → Span W gen (W.oplus a b)

/-- Additivity of a unary operation along `oplus`: what the corpus's `Sig.Hom` asks of the first symbol. -/
def Additive {V : Type*} (W : Sig V) (f : V → V) : Prop :=
  ∀ a b, f (W.oplus a b) = W.oplus (f a) (f b)

/-- **An additive operation is determined by the generators.**  Two additive maps agreeing on `gen` agree
on everything `gen` spans. -/
theorem agree_of_gen {V : Type*} (W : Sig V) (gen : V → Prop) (f g : V → V)
    (hf : Additive W f) (hg : Additive W g) (h : ∀ v, gen v → f v = g v) :
    ∀ v, Span W gen v → f v = g v := by
  intro v hv
  induction hv with
  | base hg' => exact h _ hg'
  | oplus _ _ ih1 ih2 => rw [hf, hg, ih1, ih2]

/-- **The form a run can check.**  The generators need not be observations of shown states: it is enough
that the shown data **pin** the operation on them.  This is the hypothesis the measurement tests, and
separating it matters -- with sub-structures as generators the shown pairs bound the operation from above
and force it from below, and only when the two coincide is anything determined. -/
theorem continuation_unique_of_pinned {ι St V : Type*} (O : ι → St → V)
    (rho rho' : St → St) (W : ι → Sig V) (op op' : ι → V → V) (gen : ι → V → Prop)
    (hom : ∀ i x, O i (rho x) = op i (O i x))
    (hom' : ∀ i x, O i (rho' x) = op' i (O i x))
    (add : ∀ i, Additive (W i) (op i)) (add' : ∀ i, Additive (W i) (op' i))
    (span : ∀ i x, Span (W i) (gen i) (O i x))
    (pinned : ∀ i v, gen i v → op i v = op' i v)
    (faith : Faithful O) :
    ∀ x, rho x = rho' x := fun x =>
  faith _ _ fun i => by
    rw [hom, hom', agree_of_gen (W i) (gen i) _ _ (add i) (add' i) (pinned i) _ (span i x)]

/-- A generator that **is** the observation of a shown state is pinned, because the two continuations
agree there.  So `continuation_unique` is the special case of the checkable form. -/
theorem pinned_of_shown {ι St V : Type*} (O : ι → St → V) (shown : St → Prop)
    (rho rho' : St → St) (op op' : ι → V → V) (gen : ι → V → Prop)
    (hom : ∀ i x, O i (rho x) = op i (O i x))
    (hom' : ∀ i x, O i (rho' x) = op' i (O i x))
    (shownGen : ∀ i v, gen i v → ∃ y, shown y ∧ O i y = v)
    (agree : ∀ y, shown y → rho y = rho' y) :
    ∀ i v, gen i v → op i v = op' i v := by
  rintro i v hv
  obtain ⟨y, hy, hOy⟩ := shownGen i v hv
  calc op i v = O i (rho y) := by rw [← hOy, hom]
    _ = O i (rho' y) := by rw [agree y hy]
    _ = op' i v := by rw [hom', hOy]

/-- **The guarantee of a complete solution, with the condition moved to the generators.**

Two continuations that are seen homomorphically through one faithful family, whose observed operations are
additive, and that agree on the shown states, **agree everywhere** -- provided each generator of each
observed world is the observation of some shown state.  Nothing is assumed about the asked states: they
need not have been shown, nor observed as any shown state is.

That is the complete-solution guarantee in the only form the corpus allows.  The data no longer have to
exhibit the answer; they have to exhibit the **generators**. -/
theorem continuation_unique {ι St V : Type*} (O : ι → St → V) (shown : St → Prop)
    (rho rho' : St → St) (W : ι → Sig V) (op op' : ι → V → V) (gen : ι → V → Prop)
    (hom : ∀ i x, O i (rho x) = op i (O i x))
    (hom' : ∀ i x, O i (rho' x) = op' i (O i x))
    (add : ∀ i, Additive (W i) (op i)) (add' : ∀ i, Additive (W i) (op' i))
    (span : ∀ i x, Span (W i) (gen i) (O i x))
    (shownGen : ∀ i v, gen i v → ∃ y, shown y ∧ O i y = v)
    (agree : ∀ y, shown y → rho y = rho' y)
    (faith : Faithful O) :
    ∀ x, rho x = rho' x :=
  continuation_unique_of_pinned O rho rho' W op op' gen hom hom' add add' span
    (pinned_of_shown O shown rho rho' op op' gen hom hom' shownGen agree) faith

/-- The two hypotheses are independent, and dropping generation loses the guarantee: with a world that is
**not** generated by the shown observations, two additive continuations agree on everything shown and
differ on what is asked. -/
theorem generation_needed :
    ∃ (O : Unit → Bool → Bool) (shown : Bool → Prop) (rho rho' : Bool → Bool)
      (W : Unit → Sig Bool) (op op' : Unit → Bool → Bool),
      (∀ i x, O i (rho x) = op i (O i x)) ∧ (∀ i x, O i (rho' x) = op' i (O i x)) ∧
      (∀ i, Additive (W i) (op i)) ∧ (∀ i, Additive (W i) (op' i)) ∧
      (∀ y, shown y → rho y = rho' y) ∧ Faithful O ∧ ∃ x, rho x ≠ rho' x := by
  refine ⟨fun _ x => x, fun x => x = false, id, fun _ => false, fun _ => ⟨fun a _ => a, fun a _ => a, id⟩,
    fun _ x => x, fun _ _ => false, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    ?_, ?_, ⟨true, by simp⟩⟩
  · rintro y rfl; rfl
  · intro x y h; simpa using h ()


/-! ### The operation over a cover of `Q × Q` (v0.23 §3)

Additivity along `oplus` says a part's image does not depend on the other parts.  Measurement refutes it:
where every other hypothesis holds, the true continuation is not additive.  The corpus predicts exactly
this and says where to go -- the atlas of full presentations assumes any two operands share a chart, and
the **product atlas** exists because they need not; the operation lives over a cover of `Q × Q`.

So the operation is binary: `k z v` is what the part `v` becomes **in the context** `z`, and `z` is itself
an observation, `ctx (O x)`.  Additivity is then asked of `k z` for each fixed `z`, which is a strictly
weaker demand than additivity of the operation itself, and the theorem goes through unchanged per context.

What that buys is not free, and the theorem shows the price rather than hiding it: pinning is now required
on **pairs** `(context, generator)`, so a finer context makes additivity easier and pinning harder.  That
is the same coarse/fine tension as everywhere in the corpus, here stated at the level of the signature: a
constant context is the previous theorem, a context that is the whole observation makes `k` a table again.
-/

/-- **The guarantee with the operation over pairs.**  Two continuations seen through one faithful family,
each additive **in its own context**, and pinned on the generators that occur in the contexts that occur,
agree everywhere.  `continuation_unique_of_pinned` is the case of a constant context. -/
theorem continuation_unique_in_context {ι St V : Type*} (O : ι → St → V)
    (rho rho' : St → St) (W : ι → Sig V) (ctx : ι → V → V) (k k' : ι → V → V → V)
    (gen : ι → V → V → Prop)
    (hom : ∀ i x, O i (rho x) = k i (ctx i (O i x)) (O i x))
    (hom' : ∀ i x, O i (rho' x) = k' i (ctx i (O i x)) (O i x))
    (add : ∀ i z, Additive (W i) (k i z)) (add' : ∀ i z, Additive (W i) (k' i z))
    (span : ∀ i x, Span (W i) (gen i (ctx i (O i x))) (O i x))
    (pinned : ∀ i z v, gen i z v → k i z v = k' i z v)
    (faith : Faithful O) :
    ∀ x, rho x = rho' x := fun x =>
  faith _ _ fun i => by
    rw [hom, hom', agree_of_gen (W i) (gen i (ctx i (O i x))) _ _ (add i _) (add' i _)
      (pinned i _) _ (span i x)]

/-- The constant context is the previous theorem, so nothing was lost by generalising. -/
theorem continuation_unique_of_pinned_of_context {ι St V : Type*} (O : ι → St → V)
    (rho rho' : St → St) (W : ι → Sig V) (op op' : ι → V → V) (gen : ι → V → Prop)
    (hom : ∀ i x, O i (rho x) = op i (O i x))
    (hom' : ∀ i x, O i (rho' x) = op' i (O i x))
    (add : ∀ i, Additive (W i) (op i)) (add' : ∀ i, Additive (W i) (op' i))
    (span : ∀ i x, Span (W i) (gen i) (O i x))
    (pinned : ∀ i v, gen i v → op i v = op' i v)
    (faith : Faithful O) :
    ∀ x, rho x = rho' x :=
  continuation_unique_in_context O rho rho' W (fun _ v => v) (fun i _ => op i) (fun i _ => op' i)
    (fun i _ => gen i) hom hom' (fun i _ => add i) (fun i _ => add' i) span
    (fun i _ => pinned i) faith

/-- **The price, stated as a theorem rather than as prose.**  A context fine enough to make every
continuation additive always exists -- take the observation itself, which a faithful family determines the
state by -- and then `k` is pinned only where the whole observation has been seen, which is the lookup
reading again.  So refining the context is never free: it buys additivity with pinning, and the guarantee
lives strictly between the two ends. -/
theorem context_makes_additive {St V : Type*} (O : St → V) (rho : St → St)
    (hinj : Function.Injective O) :
    ∃ (W : Sig V) (k : V → V → V), (∀ x, O (rho x) = k (O x) (O x)) ∧ ∀ z, Additive W (k z) := by
  classical
  refine ⟨⟨fun a _ => a, fun a _ => a, id⟩,
    fun z _ => if hz : ∃ x, O x = z then O (rho hz.choose) else z, fun x => ?_, fun _ _ _ => rfl⟩
  have hx : ∃ y, O y = O x := ⟨x, rfl⟩
  show O (rho x) = if hz : ∃ y, O y = O x then O (rho hz.choose) else O x
  rw [dif_pos hx, hinj hx.choose_spec]


/-! ### The symbol the solver was not using

Measurement says the additive reading **under-covers**: with the operation taken as the largest choice the
shown pairs permit, a median of 38 of 100 carriers of the answer are claimed by nobody, while almost
nothing is claimed twice.  The why-chain ends at a missing constraint rather than at a restatement --
nothing in `Additive` links a part's image to the part's place, so a part may claim anything anywhere, no
carrier of the answer has a unique possible bearer, and therefore nothing is forced.

The signature already carries the missing constraint and the solver was using two thirds of it.  `Sig` is
`oplus, ominus, rho`, and a `Sig.Hom` preserves **difference** as well as union.  Disjointness is
expressible with difference alone -- `a` and `b` are disjoint when `a ⊖ b = a` -- so an operation that
preserves `ominus` carries disjointness to the images.  The parts of a side are disjoint by construction,
hence so are their images, hence every carrier of the answer has exactly one bearer, hence the system is
determined.  That is not an extra assumption bolted on: it is the third symbol.
-/

/-- Disjointness said with the signature's difference alone. -/
def Apart {V : Type*} (W : Sig V) (a b : V) : Prop := W.ominus a b = a

/-- **An operation preserving difference carries disjointness to the images.**  So the images of the parts
of one side are disjoint, and a carrier of the answer has exactly one possible bearer. -/
theorem apart_of_hom {V : Type*} (W : Sig V) (f : V → V)
    (hf : ∀ a b, f (W.ominus a b) = W.ominus (f a) (f b)) {a b : V} (h : Apart W a b) :
    Apart W (f a) (f b) := by
  unfold Apart at h ⊢; rw [← hf, h]

/-- Preserving difference is strictly more than being additive: an additive operation may send two
disjoint parts to the same value, and then nothing about the answer is forced. -/
theorem additive_not_apart :
    ∃ (W : Sig Bool) (f : Bool → Bool) (a b : Bool),
      Additive W f ∧ Apart W a b ∧ ¬ Apart W (f a) (f b) := by
  refine ⟨⟨fun a _ => a, fun a b => if b then false else a, id⟩, fun _ => true, false, true,
    fun _ _ => rfl, by simp [Apart], by simp [Apart]⟩


/-! ### Why no certificate computed on the sample can be sound

The solver line tried five representations, each keyed by a different invariant -- the class of a state, the
orbit of a part, the orbit of a part together with its standing among the others -- and each certified its
answer by the same two checks: the shown continuations **factor through the key**, and the asked key **was
shown**.  Four of the five then certified an answer at a state where two continuations consistent with
everything shown disagree.

That is not five accidents.  For **any** key whatsoever the certificate is satisfied by two continuations
differing at any unshown state, because factoring is only ever checked where the continuation is known.  The
theorem below says exactly that, and it is the reason the question "can the answer be proved rather than
searched for" has the answer it has: not from a certificate on the sample.  What is needed instead is what
the SRT line calls de-abstraction -- the key must be justified as **the** structure of the source, not merely
as something the samples have not yet refuted.  That is a statement about the source, and no amount of
checking on the sample replaces it.
-/

/-- **No sample certificate is sound.**  Let `kappa` be any key and let the continuation `rho` factor
through it on the shown states.  Then for every unshown state there is a rival continuation that factors
through `kappa` on the shown states just as well, agrees with `rho` everywhere shown, and differs there.

So "the shown continuations factor through the key" and "the asked key was shown" together never determine
the answer, whatever the key is. -/
theorem no_certificate_is_sound {St K V : Type*} (kappa : St → K) (shown : St → Prop)
    (rho : St → V) (x : St) (hx : ¬ shown x) (v w : V) (hvw : v ≠ w)
    (h : ∀ a b, shown a → shown b → kappa a = kappa b → rho a = rho b) :
    ∃ rho' : St → V,
      (∀ a b, shown a → shown b → kappa a = kappa b → rho' a = rho' b) ∧
      (∀ a, shown a → rho' a = rho a) ∧ rho' x ≠ rho x := by
  classical
  refine ⟨Function.update rho x (if rho x = v then w else v), ?_, ?_, ?_⟩
  · intro a b ha hb hk
    have hax : a ≠ x := fun e => hx (e ▸ ha)
    have hbx : b ≠ x := fun e => hx (e ▸ hb)
    rw [Function.update_of_ne hax, Function.update_of_ne hbx]
    exact h a b ha hb hk
  · intro a ha
    have hax : a ≠ x := fun e => hx (e ▸ ha)
    exact Function.update_of_ne hax _ _
  · rw [Function.update_self]
    by_cases hv : rho x = v
    · rw [if_pos hv, hv]
      exact fun e => hvw e.symm
    · rw [if_neg hv]
      exact fun e => hv e.symm


/-! ### The certificate that **is** sound, and the debt it leaves explicit

`no_certificate_is_sound` refutes the certificate "the shown continuations factor through the key".  It does
not refute the neighbouring statement, and the difference is the whole of P5.

The rival it builds agrees with the shown data and factors through the key **there**, but it does not factor
through the key everywhere -- that is how it is built.  So if the class is frozen first,

    C(kappa) = { rho : rho factors through kappa }

then the rival is outside `C(kappa)`, and inside `C(kappa)` the certificate becomes sound: a key that was
shown pins the answer, because there is only one member of the class that can agree.

The debt does not disappear; it becomes a single named statement about the **source** rather than a hidden
appeal to the sample: *the truth lies in `C(kappa)`*.  That is exactly what the SRT line calls de-abstraction
-- the designed object must be shown to be the actual one -- and it is the only thing left to establish.
Everything else is then a projection.
-/

/-- Membership of the frozen class: the continuation is a function of the key. -/
def Factors {St K V : Type*} (kappa : St → K) (rho : St → V) : Prop :=
  ∀ a b, kappa a = kappa b → rho a = rho b

/-- **Uniqueness in a frozen class is a sound certificate.**  If the truth lies in the class, the shown
answers determine it at every state whose key was shown -- and the conclusion is an equality with the truth,
not a consistency claim.

Contrast with `no_certificate_is_sound`, which builds a rival for the *same* shown data: that rival is not in
the class, so the two theorems do not compete.  What separates them is only whether the class was frozen
before the sample was consulted. -/
theorem sound_relative_to_class {St K V : Type*} (kappa : St → K) (shown : St → Prop)
    (truth : St → V) (h : Factors kappa truth) {x y : St} (hy : shown y)
    (hk : kappa x = kappa y) : truth x = truth y := h x y hk

/-- And the debt is not vacuous: for any key that glues two states the demonstrations do not separate, there
is a continuation **outside** the class agreeing with everything shown.  So "the truth lies in the class" is a
real statement about the source and cannot be discharged by looking at the sample. -/
theorem class_debt_is_real {St K : Type*} (kappa : St → K) (shown : St → Prop)
    (x y : St) (hx : ¬ shown x) (hxy : kappa x = kappa y) (hne : x ≠ y) :
    ∃ rho : St → Bool, (∀ a, shown a → rho a = false) ∧ ¬ Factors kappa rho := by
  classical
  refine ⟨Function.update (fun _ => false) x true, ?_, ?_⟩
  · intro a ha
    have hax : a ≠ x := fun e => hx (e ▸ ha)
    exact Function.update_of_ne hax _ _
  · intro hf
    have h1 : Function.update (fun _ : St => false) x true x = true := Function.update_self _ _ _
    have h2 : Function.update (fun _ : St => false) x true y = false :=
      Function.update_of_ne (Ne.symm hne) _ _
    exact absurd ((h1.symm.trans (hf x y hxy)).trans h2) (by simp)

end Solution

end MetaLang.Solver
