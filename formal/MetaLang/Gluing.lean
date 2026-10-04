import MetaLang.MeaningWitnesses

/-!
# Completing the ASC topology, gluing charts, and grammar expansion
(v0.18–v0.20)

The three threads that were missing after N1–N2 and N8.

**Scales.** `sep_le_sep_transport_succ` gives a single step; here comes the
word: transport along a word of length `k` stretches the depth by at most
`k`, and in the real-valued scale by a factor of at most `2^k` (v0.19 `S4`,
`S6`).

**Locality.** A chart closed under the transitions carries **the same**
filtration and the same distinguishing depth as the ambient machine; hence,
for a cover in which every pair lies inside a single chart, the global
semantics is fully recovered from the local ones (v0.20 `S8`, `S9`).

**Grammar growth.** Enlarging the set of actions refines the topology, and
the refinement can be strict; but adding a synonym changes nothing (v0.18
`S11`, `S12`; v0.20 `S10`).
-/

namespace MetaLang

universe u

namespace Machine

open scoped Classical

variable {M : Machine}

/-! ## Transport along a word: the `2^k` bound -/

theorem sep_le_sep_transport_add :
    ∀ (w : List M.Act) (x y : M.St),
      M.sep x y ≤ M.sep (M.transport w x) (M.transport w y) + w.length := by
  intro w
  induction w with
  | nil => intro x y; simpa using le_refl (M.sep x y)
  | cons a w ih =>
      intro x y
      have h1 : M.sep x y ≤ M.sep (M.T a x) (M.T a y) + 1 :=
        sep_le_sep_transport_succ a x y
      have h2 : M.sep (M.T a x) (M.T a y) ≤
          M.sep (M.transport w (M.T a x)) (M.transport w (M.T a y)) + w.length := ih _ _
      have h3 : M.sep (M.T a x) (M.T a y) + 1 ≤
          (M.sep (M.transport w (M.T a x)) (M.transport w (M.T a y)) + w.length) + 1 :=
        add_le_add h2 le_rfl
      refine le_trans h1 (le_trans h3 (le_of_eq ?_))
      simp [List.length_cons, add_assoc]

/-- The real-valued scale under a depth shift by `k`. -/
theorem dOf_add_natCast (a : ℕ∞) (k : ℕ) :
    dOf (a + (k : ℕ∞)) = (2 : ℝ) ^ (-(k : ℤ)) * dOf a := by
  cases a with
  | top => simp
  | coe n =>
      have : ((n : ℕ∞) + (k : ℕ∞)) = ((n + k : ℕ) : ℕ∞) := by push_cast; rfl
      rw [this, dOf_coe, dOf_coe, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      congr 1
      push_cast
      ring

/-- **The `2^k` bound (gate `S6` of v0.19).** Transport along a word of
length `k` stretches the continuation distance by a factor of at most
`2^k`. -/
theorem dASC_transport_le (w : List M.Act) (x y : M.St) :
    M.dASC (M.transport w x) (M.transport w y) ≤
      (2 : ℝ) ^ (w.length : ℤ) * M.dASC x y := by
  have hd := dOf_antitone (sep_le_sep_transport_add w x y)
  rw [dOf_add_natCast] at hd
  have hzero : (w.length : ℤ) + (-(w.length : ℤ)) = 0 := by ring
  have key : M.dASC (M.transport w x) (M.transport w y)
      = (2 : ℝ) ^ (w.length : ℤ) *
        ((2 : ℝ) ^ (-(w.length : ℤ)) * M.dASC (M.transport w x) (M.transport w y)) := by
    rw [← mul_assoc, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), hzero, zpow_zero, one_mul]
  rw [key]
  exact mul_le_mul_of_nonneg_left hd (by positivity)

/-- **Primitives are at most 2-Lipschitz (gate `S4` of v0.19).** -/
theorem dASC_step_le (a : M.Act) (x y : M.St) :
    M.dASC (M.T a x) (M.T a y) ≤ 2 * M.dASC x y := by
  have := dASC_transport_le [a] x y
  simpa using this

/-! ## A single idempotent generator: collapse in one step -/

/-- A machine with a single idempotent continuation (v0.18 §"single
generator", v0.19 `S3`). -/
structure SingleGenerator (M : Machine) where
  /-- The only action. -/
  act : M.Act
  /-- There are no other actions. -/
  only : ∀ a : M.Act, a = act
  /-- It is idempotent. -/
  idem : ∀ x : M.St, M.T act (M.T act x) = M.T act x

theorem SingleGenerator.transport_cons (h : SingleGenerator M) :
    ∀ (w : List M.Act) (x : M.St), M.transport (h.act :: w) x = M.T h.act x := by
  intro w
  induction w with
  | nil => intro x; rfl
  | cons b w ih =>
      intro x
      have hb : b = h.act := h.only b
      subst hb
      have := ih (M.T h.act x)
      simpa [Machine.transport, h.idem] using this

/-- **Collapse in one step (gates `S6` of v0.18, `S3` of v0.19).** With a
single idempotent generator the refinement stabilizes at depth 1. -/
theorem SingleGenerator.indist_iff_approx_one (h : SingleGenerator M) (x y : M.St) :
    M.Indist x y ↔ M.approx 1 x y := by
  constructor
  · intro hi
    exact approx_of_indist 1 hi
  · intro ha w
    cases w with
    | nil => exact ha.1
    | cons b w =>
        have hb : b = h.act := h.only b
        subst hb
        rw [h.transport_cons w x, h.transport_cons w y]
        exact ha.2 h.act

end Machine

/-! ## A chart closed under the transitions -/

/-- A local chart: a subset closed under all continuations. -/
structure Subchart (M : Machine) where
  /-- The carrier of the chart. -/
  carrier : Set M.St
  /-- Closedness under the transitions. -/
  closed : ∀ (a : M.Act) (x : M.St), x ∈ carrier → M.T a x ∈ carrier

namespace Subchart

variable {M : Machine} (C : Subchart M)

/-- The chart as a machine in its own right. -/
def machine : Machine where
  St := {x : M.St // x ∈ C.carrier}
  Act := M.Act
  Resp := M.Resp
  T := fun a x => ⟨M.T a x.1, C.closed a x.1 x.2⟩
  R := fun x => M.R x.1

/-- **The local filtration coincides with the global one (gate `S8` of v0.20).** -/
theorem approx_iff : ∀ (n : ℕ) (x y : C.machine.St),
    C.machine.approx n x y ↔ M.approx n x.1 y.1 := by
  intro n
  induction n with
  | zero => intro x y; exact Iff.rfl
  | succ n ih =>
      intro x y
      constructor
      · rintro ⟨h0, hstep⟩
        exact ⟨h0, fun a => (ih _ _).mp (hstep a)⟩
      · rintro ⟨h0, hstep⟩
        exact ⟨h0, fun a => (ih _ _).mpr (hstep a)⟩

open scoped Classical in
/-- **The distinguishing depth is preserved by gluing (gate `S9` of v0.20).** -/
theorem sep_eq (x y : C.machine.St) : C.machine.sep x y = M.sep x.1 y.1 := by
  apply le_antisymm
  · refine Machine.le_of_forall_natCast_lt fun n hn => ?_
    exact (Machine.approx_iff_lt_sep n _ _).mp
      ((C.approx_iff n x y).mp ((Machine.approx_iff_lt_sep n x y).mpr hn))
  · refine Machine.le_of_forall_natCast_lt fun n hn => ?_
    exact (Machine.approx_iff_lt_sep n x y).mp
      ((C.approx_iff n x y).mpr ((Machine.approx_iff_lt_sep n _ _).mpr hn))

/-- The local semantics agrees with the global one on the carrier of the chart. -/
theorem indist_iff (x y : C.machine.St) :
    C.machine.Indist x y ↔ M.Indist x.1 y.1 := by
  rw [Machine.indist_iff_forall_approx, Machine.indist_iff_forall_approx]
  exact forall_congr' fun n => C.approx_iff n x y

end Subchart

/-! ## Reconstruction from local charts (v0.21) -/

namespace Machine

variable {M : Machine}

/-- A cover by closed charts in which every **pair** lies inside a single
chart. This is the tuple-cover condition of v0.23 in topological form. -/
structure ChartAtlas (M : Machine) where
  /-- Chart indices. -/
  ι : Type u
  /-- The charts themselves. -/
  chart : ι → Subchart M
  /-- Every pair of points lies in a common chart. -/
  pair_cover : ∀ x y : M.St, ∃ i, x ∈ (chart i).carrier ∧ y ∈ (chart i).carrier

/-- **Behavioural descent recovers the semantic quotient (gates `S1`, `S2`
of v0.21).** Global indistinguishability is fully determined by the local
ones: no appeal to a `Q` known in advance. -/
theorem indist_from_charts (A : ChartAtlas M) (x y : M.St) :
    M.Indist x y ↔
      ∃ (i : A.ι) (hx : x ∈ (A.chart i).carrier) (hy : y ∈ (A.chart i).carrier),
        (A.chart i).machine.Indist ⟨x, hx⟩ ⟨y, hy⟩ := by
  constructor
  · intro h
    obtain ⟨i, hx, hy⟩ := A.pair_cover x y
    exact ⟨i, hx, hy, (Subchart.indist_iff _ _ _).mpr h⟩
  · rintro ⟨i, hx, hy, h⟩
    exact (Subchart.indist_iff _ _ _).mp h

/-- **The local filtration recovers the ASC filtration (gates `S3`, `S4` of
v0.21).** -/
theorem approx_from_charts (A : ChartAtlas M) (n : ℕ) (x y : M.St) :
    M.approx n x y ↔
      ∃ (i : A.ι) (hx : x ∈ (A.chart i).carrier) (hy : y ∈ (A.chart i).carrier),
        (A.chart i).machine.approx n ⟨x, hx⟩ ⟨y, hy⟩ := by
  constructor
  · intro h
    obtain ⟨i, hx, hy⟩ := A.pair_cover x y
    exact ⟨i, hx, hy, (Subchart.approx_iff _ n _ _).mpr h⟩
  · rintro ⟨i, hx, hy, h⟩
    exact (Subchart.approx_iff _ n _ _).mp h

open scoped Classical in
/-- **The geometry of depths is preserved (gates `S5`, `S6` of v0.21).** -/
theorem sep_from_charts (A : ChartAtlas M) (x y : M.St)
    {i : A.ι} (hx : x ∈ (A.chart i).carrier) (hy : y ∈ (A.chart i).carrier) :
    (A.chart i).machine.sep ⟨x, hx⟩ ⟨y, hy⟩ = M.sep x y :=
  Subchart.sep_eq _ _ _

end Machine

/-! ## Grammar growth -/

/-- A grammar expansion: the same states and responses, more continuations. -/
structure Expansion where
  /-- States. -/
  St : Type u
  /-- Responses. -/
  Resp : Type u
  /-- The old continuations. -/
  Act₀ : Type u
  /-- The new continuations. -/
  Act₁ : Type u
  /-- The embedding of the old into the new. -/
  emb : Act₀ → Act₁
  /-- The action of the expanded grammar. -/
  T : Act₁ → St → St
  /-- The response. -/
  R : St → Resp

namespace Expansion

variable (E : Expansion)

/-- The machine of the old grammar. -/
abbrev base : Machine := ⟨E.St, E.Act₀, E.Resp, fun a => E.T (E.emb a), E.R⟩

/-- The machine of the expanded grammar. -/
abbrev full : Machine := ⟨E.St, E.Act₁, E.Resp, E.T, E.R⟩

variable {E}

/-- **A grammar expansion refines the topology (gate `S11` of v0.18).** -/
theorem approx_full_imp_base :
    ∀ (n : ℕ) (x y : E.St), E.full.approx n x y → E.base.approx n x y := by
  intro n
  induction n with
  | zero => intro x y h; exact h
  | succ n ih =>
      rintro x y ⟨h0, hstep⟩
      exact ⟨h0, fun a => ih _ _ (hstep (E.emb a))⟩

theorem indist_full_imp_base (x y : E.St) :
    E.full.Indist x y → E.base.Indist x y := by
  intro h
  refine Machine.indist_of_forall_approx fun n => ?_
  exact approx_full_imp_base n x y (Machine.approx_of_indist n h)

open scoped Classical in
/-- The distinguishing depth in the expanded grammar is no larger. -/
theorem sep_full_le_base (x y : E.St) : E.full.sep x y ≤ E.base.sep x y := by
  refine Machine.le_of_forall_natCast_lt fun n hn => ?_
  exact (Machine.approx_iff_lt_sep (M := E.base) n x y).mp
    (approx_full_imp_base n x y ((Machine.approx_iff_lt_sep (M := E.full) n x y).mpr hn))

/-- **A synonym changes nothing (gates `S10` of v0.20, `S7` of v0.21).** If
every new continuation acts like some old one, the expansion does not refine
the topology. -/
theorem approx_base_imp_full
    (hsyn : ∀ b : E.Act₁, ∃ a : E.Act₀, ∀ x : E.St, E.T b x = E.T (E.emb a) x) :
    ∀ (n : ℕ) (x y : E.St), E.base.approx n x y → E.full.approx n x y := by
  intro n
  induction n with
  | zero => intro x y h; exact h
  | succ n ih =>
      rintro x y ⟨h0, hstep⟩
      refine ⟨h0, fun b => ?_⟩
      obtain ⟨a, ha⟩ := hsyn b
      have hstep' := ih (E.T (E.emb a) x) (E.T (E.emb a) y) (hstep a)
      show E.full.approx n (E.T b x) (E.T b y)
      rw [ha x, ha y]
      exact hstep'

end Expansion

/-! ## Witnesses -/

namespace GrammarWitness

/-- An expansion that adds a **new** distinction: with no actions the states
`0` and `1` are indistinguishable; with one action they are separated at
depth 1. -/
abbrev strictExp : Expansion.{0} where
  St := Fin 3
  Resp := Bool
  Act₀ := Empty
  Act₁ := Unit
  emb := fun e => e.elim
  T := fun _ s => if s = 0 then 2 else s
  R := fun s => s = 2

theorem base_indist_zero_one : strictExp.base.Indist 0 1 := by
  intro w
  cases w with
  | nil => rfl
  | cons a _ => exact a.elim

/-- **An expansion can be strict (gate `S12` of v0.18).** -/
theorem full_separates_zero_one : ¬ strictExp.full.Indist 0 1 := by
  intro h
  have := h [()]
  revert this
  decide

/-- **The intermediate topology is nontrivial (gate `S13` of v0.18).**
Between the old and the new topology the distance does not collapse: a pair
glued before the expansion has finite depth after it. -/
theorem intermediate_nontrivial :
    strictExp.base.Indist 0 1 ∧ ¬ strictExp.full.Indist 0 1 :=
  ⟨base_indist_zero_one, full_separates_zero_one⟩

end GrammarWitness

/-! ## Multiscale behaviour on the infinite witness -/

namespace Multiscale

open Witnesses

/-- The sequence that differs from the zero one exactly at coordinate `n`. -/
def spike (n : ℕ) : ℕ → Bool := fun i => decide (i = n)

theorem spike_approx (n k : ℕ) (h : k < n) :
    (shiftMachine Bool).approx k (fun _ => false) (spike n) := by
  refine (shift_approx k _ _).mpr fun i hi => ?_
  have : i ≠ n := by omega
  simp [spike, this]

theorem spike_not_approx (n : ℕ) :
    ¬ (shiftMachine Bool).approx n (fun _ => false) (spike n) := by
  intro h
  have := (shift_approx n _ _).mp h n (Nat.le_refl n)
  simp [spike] at this

open scoped Classical in
/-- **There is an activation witness at every depth (gates `S9` of v0.18,
`S9` of v0.19).** For every `n` there is a pair of states separated exactly
at depth `n`. -/
theorem exists_sep_eq (n : ℕ) :
    ∃ x y : ℕ → Bool, (shiftMachine Bool).sep x y = n := by
  refine ⟨fun _ => false, spike n, le_antisymm ?_ ?_⟩
  · by_contra hlt
    push_neg at hlt
    exact spike_not_approx n ((Machine.approx_iff_lt_sep n _ _).mpr hlt)
  · by_contra hlt
    push_neg at hlt
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
    have hmn : m < n := by
      rw [← hm] at hlt
      exact Nat.cast_lt.mp hlt
    have hcontra : (m : ℕ∞) < (shiftMachine Bool).sep (fun _ => false) (spike n) :=
      (Machine.approx_iff_lt_sep m _ _).mp (spike_approx n m hmn)
    rw [← hm] at hcontra
    exact absurd hcontra (lt_irrefl _)

/-- **The behavioural scale stays one while the ASC scale decreases (gate
`S14` of v0.19).** For every `n` there is a semantically distinct pair at
continuation distance `2^{-n}`. -/
theorem scales_separate (n : ℕ) :
    ∃ x y : ℕ → Bool,
      ¬ (shiftMachine Bool).Indist x y ∧
        (shiftMachine Bool).dASC x y = (2 : ℝ) ^ (-(n : ℤ)) := by
  obtain ⟨x, y, hsep⟩ := exists_sep_eq n
  refine ⟨x, y, ?_, ?_⟩
  · intro h
    rw [(Machine.sep_eq_top_iff (M := shiftMachine Bool) x y).mpr h] at hsep
    exact absurd hsep (by simp)
  · show Machine.dOf ((shiftMachine Bool).sep x y) = (2 : ℝ) ^ (-(n : ℤ))
    rw [hsep]
    exact Machine.dOf_coe n

end Multiscale

/-! ## A cover witness with overlap and exclusive regions -/

namespace CoverWitness

/-- A cover of `Fin 3` by two charts: "not 2" and "not 0". -/
abbrev twoCharts : Cover (Fin 3) where
  ι := Bool
  chart := fun b => {x : Fin 3 | if b then x ≠ 2 else x ≠ 0}

/-- **The overlap is nonempty (gate `S3` of v0.20).** -/
theorem overlap_nonempty :
    ((twoCharts.chart true) ∩ (twoCharts.chart false)).Nonempty := by
  refine ⟨1, ?_, ?_⟩
  · show (1 : Fin 3) ≠ 2
    decide
  · show (1 : Fin 3) ≠ 0
    decide

/-- **Every chart has an exclusive region (gate `S4` of v0.20).** -/
theorem exclusive_regions :
    (0 : Fin 3) ∈ twoCharts.chart true ∧ (0 : Fin 3) ∉ twoCharts.chart false ∧
    (2 : Fin 3) ∈ twoCharts.chart false ∧ (2 : Fin 3) ∉ twoCharts.chart true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (0 : Fin 3) ≠ 2
    decide
  · show ¬ ((0 : Fin 3) ≠ 0)
    decide
  · show (2 : Fin 3) ≠ 0
    decide
  · show ¬ ((2 : Fin 3) ≠ 2)
    decide

theorem covers : twoCharts.Covers := by
  intro q
  by_cases h : q = 0
  · refine ⟨true, ?_⟩
    show q ≠ 2
    rw [h]
    decide
  · exact ⟨false, h⟩

end CoverWitness

/-! ## The spectator observer and the depth of descent (v0.21) -/

namespace Spectator

variable {M : Machine.{u}} (B : Type u)

/-- A machine with a "spectator": the second coordinate affects neither the
transitions nor the responses. -/
abbrev machine (M : Machine.{u}) (B : Type u) : Machine.{u} where
  St := M.St × B
  Act := M.Act
  Resp := M.Resp
  T := fun a p => (M.T a p.1, p.2)
  R := fun p => M.R p.1

theorem transport_fst (w : List M.Act) (p : M.St × B) :
    (machine M B).transport w p = (M.transport w p.1, p.2) := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih => simpa using ih (M.T a p.1, p.2)

/-- **Spectator presentations are semantically coequalized (gate `S8` of
v0.21).** A distinction invisible to every continuation is erased by the
semantic quotient. -/
theorem spectator_collapsed (x : M.St) (b b' : B) :
    (machine M B).Indist (x, b) (x, b') := by
  intro w
  rw [transport_fst, transport_fst]

end Spectator

namespace DescentDepth

open Separation

/-- **The response alone is not enough (gate `S13` of v0.21).** Agreement of
the immediate responses does not imply semantic identity. -/
theorem response_only_breaks_descent :
    depthMachine.approx 0 0 1 ∧ ¬ depthMachine.Indist 0 1 :=
  ⟨depth_approx_zero, fun h => absurd (depth_indist_eq h) (by decide)⟩

/-- **One round is not enough (gate `S12` of v0.21).** The states `1` and
`3` agree up to depth 1 and are nevertheless semantically distinct. -/
theorem one_round_insufficient :
    depthMachine.approx 1 1 3 ∧ ¬ depthMachine.Indist 1 3 := by
  refine ⟨⟨rfl, fun _ => rfl⟩, fun h => absurd (depth_indist_eq h) (by decide)⟩

/-- **A misaligned interface blocks direct descent (gate `S14` of v0.21).**
An interface map that does not preserve responses identifies points the
semantics separates: gluing along it is impossible. -/
theorem unaligned_interface_breaks_descent {M : Machine} (f : M.St → M.St)
    (h : ¬ ∀ x : M.St, M.R (f x) = M.R x) : ∃ x : M.St, ¬ M.Indist x (f x) := by
  push_neg at h
  obtain ⟨x, hx⟩ := h
  exact ⟨x, fun hi => hx (Machine.indist_resp hi).symm⟩

/-! ## Synonyms of continuations (v0.10 `S10`) -/

namespace Synonyms

variable (M : Machine.{u})

/-- The doubled grammar: every continuation gets exactly one distinct
synonym. -/
abbrev doubled : Machine.{u} where
  St := M.St
  Act := M.Act × Bool
  Resp := M.Resp
  T := fun a s => M.T a.1 s
  R := M.R

/-- **Every continuation has a distinct semantic synonym (gate `S10` of
v0.10).** The synonym acts identically but is a different symbol: a surface
difference of symbols is not semantic. -/
theorem every_action_has_synonym (a : (doubled M).Act) :
    ∃ b : (doubled M).Act, b ≠ a ∧ ∀ s : M.St, (doubled M).T b s = (doubled M).T a s := by
  refine ⟨(a.1, !a.2), ?_, fun _ => rfl⟩
  intro h
  have : (!a.2) = a.2 := congrArg Prod.snd h
  exact absurd this (by cases a.2 <;> decide)

theorem doubled_transport (w : List ((doubled M).Act)) (s : M.St) :
    (doubled M).transport w s = M.transport (w.map Prod.fst) s := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simpa using ih (M.T a.1 s)

/-- Doubling the grammar with synonyms does not refine the semantics. -/
theorem doubled_indist_iff (s t : M.St) :
    (doubled M).Indist s t ↔ M.Indist s t := by
  constructor
  · intro h w
    have hw := h (w.map (fun a => (a, false)))
    rw [doubled_transport, doubled_transport] at hw
    have hmap : (w.map (fun a : M.Act => (a, false))).map Prod.fst = w := by
      simp [List.map_map, Function.comp_def]
    rwa [hmap] at hw
  · intro h w
    rw [doubled_transport, doubled_transport]
    exact h (w.map Prod.fst)

end Synonyms

end DescentDepth

end MetaLang
