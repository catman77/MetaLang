import MetaLang.ASCTopology

/-!
# The collapse bridge and ASC: a no-go for global nonexpansiveness (v0.19)

The book's one-step collapse topology and the rich compositional ASC
topology are compatible only as **different scales of one structure**. That
is proved here as a no-go:

> If, within a single global metric, every admissible primitive is
> nonexpansive and responses are uniformly separated, then the metric is
> uniformly discrete on semantically distinct pairs.

Consequently such a metric cannot coincide with the non-discrete ASC
geometry, where distances decay as `2^{-depth}`. The finite form of that
divergence is a **distortion of exactly `2^depth`**, which is what the gates
record
`S12`, `S15`, `S17` v0.19.
-/

namespace MetaLang

namespace Machine

open scoped Classical

variable {M : Machine}

/-- A global pseudometric in which every admissible transport is
nonexpansive. -/
structure GlobalMetric (M : Machine) where
  /-- The distance itself. -/
  rho : M.St → M.St → ℝ
  /-- Nonnegativity. -/
  nonneg : ∀ x y, 0 ≤ rho x y
  /-- Nonexpansiveness of every primitive. -/
  nonexpansive : ∀ (a : M.Act) (x y : M.St), rho (M.T a x) (M.T a y) ≤ rho x y

namespace GlobalMetric

variable (P : GlobalMetric M)

/-- Nonexpansiveness extends to words: transport along any word of contexts
does not increase the distance. -/
theorem rho_transport_le : ∀ (w : List M.Act) (x y : M.St),
    P.rho (M.transport w x) (M.transport w y) ≤ P.rho x y := by
  intro w
  induction w with
  | nil => intro x y; exact le_refl _
  | cons a w ih =>
      intro x y
      exact le_trans (ih (M.T a x) (M.T a y)) (P.nonexpansive a x y)

/-- Uniform separation of responses: a difference in the immediate response
always costs at least `δ`. -/
def UniformResponseSeparation (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ x y : M.St, M.R x ≠ M.R y → δ ≤ P.rho x y

/-- **The no-go for global nonexpansiveness.** Nonexpansiveness of all
primitives together with uniform separation of responses makes the metric
uniformly discrete: any two semantically distinct states are at least `δ`
apart, no matter at what depth they differ. -/
theorem uniformly_discrete_of_nonexpansive {δ : ℝ}
    (hsep : P.UniformResponseSeparation δ) {x y : M.St} (h : ¬ M.Indist x y) :
    δ ≤ P.rho x y := by
  obtain ⟨w, hw⟩ := exists_witness_of_not_indist h
  exact le_trans (hsep.2 _ _ hw) (P.rho_transport_le w x y)

end GlobalMetric

/-! ### The global metric of stable behaviour -/

/-- `rho_inf` — the canonical 0/1 metric on the semantic quotient. -/
noncomputable def rhoInf (M : Machine) : GlobalMetric M where
  rho x y := if M.Indist x y then 0 else 1
  nonneg x y := by
    by_cases h : M.Indist x y <;> simp [h]
  nonexpansive a x y := by
    by_cases h : M.Indist x y
    · simp [h, indist_congr h a]
    · by_cases h' : M.Indist (M.T a x) (M.T a y) <;> simp [h, h']

@[simp] theorem rhoInf_eq_zero_iff (x y : M.St) :
    (M.rhoInf).rho x y = 0 ↔ M.Indist x y := by
  by_cases h : M.Indist x y <;> simp [rhoInf, h]

theorem rhoInf_eq_one_of_not_indist {x y : M.St} (h : ¬ M.Indist x y) :
    (M.rhoInf).rho x y = 1 := by simp [rhoInf, h]

/-- **`rho_inf` is discrete**: its positive values are exactly one. It has no
intermediate scales. -/
theorem rhoInf_discrete (x y : M.St) :
    (M.rhoInf).rho x y = 0 ∨ (M.rhoInf).rho x y = 1 := by
  by_cases h : M.Indist x y
  · left; simp [rhoInf, h]
  · right; exact rhoInf_eq_one_of_not_indist h

/-- `rho_inf` does uniformly separate responses, with `δ = 1`. -/
theorem rhoInf_separation : (M.rhoInf).UniformResponseSeparation 1 := by
  refine ⟨by norm_num, fun x y hR => ?_⟩
  have : ¬ M.Indist x y := fun h => hR (indist_resp h)
  rw [rhoInf_eq_one_of_not_indist this]

/-! ### Divergence of the scales

The ASC geometry resolves depths: the distance decays as `2^{-n}`. The
global nonexpansive metric does not see this. The finite measure of the
divergence is the distortion. -/

/-- **The distortion equals `2^depth`.** Where the ASC geometry gives
`2^{-n}`, the global discrete metric gives one. -/
theorem distortion_eq {x y : M.St} {n : ℕ} (h : M.sep x y = (n : ℕ∞)) :
    (M.rhoInf).rho x y = 2 ^ n * M.dASC x y := by
  have hnot : ¬ M.Indist x y := by
    intro hind
    rw [(sep_eq_top_iff x y).mpr hind] at h
    exact absurd h.symm (by simp)
  rw [rhoInf_eq_one_of_not_indist hnot]
  unfold dASC
  rw [h, dOf_coe]
  rw [zpow_neg, zpow_natCast]
  field_simp

/-- The deeper the distinction, the wider the gap between the scales: at
depth at least 4 the distortion is at least 16 — the finite form of gate
`S12`. -/
theorem distortion_ge_of_deep {x y : M.St} {n : ℕ} (h : M.sep x y = (n : ℕ∞))
    (hn : 4 ≤ n) : (16 : ℝ) * M.dASC x y ≤ (M.rhoInf).rho x y := by
  rw [distortion_eq h]
  have hd : 0 ≤ M.dASC x y := dASC_nonneg x y
  have : (16 : ℝ) ≤ 2 ^ n := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := by
          apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
  exact mul_le_mul_of_nonneg_right this hd

/-! ### A concrete witness of the divergence

A chain of length 6: the difference between states `0` and `1` shows up only
at depth 4. The ASC geometry sees it as `2^{-4}`, the global metric as
one. -/

/-- Transport along the chain: advance, then stall at the absorbing state. -/
def chainT : Unit → Fin 6 → Fin 6 := fun _ i => ⟨min (i.val + 1) 5, by omega⟩

/-- Only the final state of the chain is observable. -/
def chainR : Fin 6 → Bool := fun i => i.val == 5

/-- A world with a deep distinction. -/
abbrev chainMachine : Machine where
  St := Fin 6
  Act := Unit
  Resp := Bool
  T := chainT
  R := chainR

theorem chain_approx3 : chainMachine.approx 3 0 1 := by
  refine ⟨rfl, ?_⟩; rintro ⟨⟩
  refine ⟨rfl, ?_⟩; rintro ⟨⟩
  refine ⟨rfl, ?_⟩; rintro ⟨⟩
  exact rfl

theorem chain_not_approx4 : ¬ chainMachine.approx 4 0 1 := by
  rintro ⟨-, h⟩
  obtain ⟨-, h⟩ := h ()
  obtain ⟨-, h⟩ := h ()
  obtain ⟨-, h⟩ := h ()
  have hfin : (false : Bool) = true := h ()
  exact Bool.noConfusion hfin

/-- The distinguishing depth equals four. -/
theorem chain_sep : chainMachine.sep 0 1 = ((4 : ℕ) : ℕ∞) := by
  have h3 : ((3 : ℕ) : ℕ∞) < chainMachine.sep 0 1 :=
    (approx_iff_lt_sep 3 0 1).mp chain_approx3
  have h4 : ¬ ((4 : ℕ) : ℕ∞) < chainMachine.sep 0 1 := fun h =>
    chain_not_approx4 ((approx_iff_lt_sep 4 0 1).mpr h)
  push_neg at h4
  have hne : chainMachine.sep 0 1 ≠ ⊤ := by
    intro htop
    rw [htop] at h4
    exact absurd h4 (by simp)
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hk] at h3 h4
  have hlt : 3 < k := Nat.cast_lt.mp h3
  have hle : k ≤ 4 := WithTop.coe_le_coe.mp h4
  have hk4 : k = 4 := by omega
  subst hk4
  exact hk.symm

theorem chain_not_indist : ¬ chainMachine.Indist 0 1 := by
  intro h
  have htop : chainMachine.sep 0 1 = ⊤ := (sep_eq_top_iff 0 1).mpr h
  rw [chain_sep] at htop
  exact absurd htop (by simp)

/-- The ASC distance on this pair is `1/16`. -/
theorem chain_dASC : chainMachine.dASC 0 1 = 1 / 16 := by
  unfold dASC
  rw [chain_sep, dOf_coe]
  norm_num

/-- **The two scales differ.** On one and the same pair the ASC geometry
gives `1/16` while the global nonexpansive metric gives one: a distortion of
exactly 16. -/
theorem scales_differ :
    ∃ (N : Machine.{0}) (x y : N.St),
      ¬ N.Indist x y ∧ N.dASC x y = 1 / 16 ∧ (N.rhoInf).rho x y = 1 :=
  ⟨chainMachine, 0, 1, chain_not_indist, chain_dASC,
   rhoInf_eq_one_of_not_indist chain_not_indist⟩

end Machine

end MetaLang
