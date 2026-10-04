import MetaLang.Congruence

/-!
# The ASC topology of continuations (v0.18)

The filtration `approx n` from `Congruence.lean` *is* the finite-depth ASC
filtration. Geometry is built on top of it here: the **distinguishing
depth**

  `sep x y = the least n at which approx n already fails`

with `sep x y = ⊤` exactly when the states are semantically identical.

The primary object is `sep`, valued in `ℕ∞`, rather than a real-valued
metric. The strong triangle inequality then takes the form

  `min (sep x y) (sep y z) ≤ sep x z`

and is proved without real arithmetic. The real-valued `d = 2^{-sep}`
follows as a corollary at the end of the file.

## Depth convention

Checked against `worldmeta/topology.py` of v0.18: `first_distinguishing_depth`
numbers levels from zero and `d = 2.0**(-dep)`, so when the immediate
responses differ, `dep = 0` and `d = 1`. This agrees with
`approx 0 s t ↔ R s = R t`.
-/

namespace MetaLang

namespace Machine

open scoped Classical

variable {M : Machine}

/-! ### `approx n` — an equivalence relation at every depth -/

theorem approx_refl : ∀ (n : ℕ) (x : M.St), M.approx n x x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ⟨rfl, fun a => ih (M.T a x)⟩

theorem approx_symm : ∀ (n : ℕ) {x y : M.St}, M.approx n x y → M.approx n y x := by
  intro n
  induction n with
  | zero => intro x y h; exact h.symm
  | succ n ih => intro x y h; exact ⟨h.1.symm, fun a => ih (h.2 a)⟩

theorem approx_trans : ∀ (n : ℕ) {x y z : M.St},
    M.approx n x y → M.approx n y z → M.approx n x z := by
  intro n
  induction n with
  | zero => intro x y z h₁ h₂; exact h₁.trans h₂
  | succ n ih =>
      intro x y z h₁ h₂
      exact ⟨h₁.1.trans h₂.1, fun a => ih (h₁.2 a) (h₂.2 a)⟩

/-! ### Distinguishing depth -/

/-- **Distinguishing depth.** The least depth at which refinement already
separates `x` and `y`; `⊤` if it never separates them. -/
noncomputable def sep (M : Machine) (x y : M.St) : ℕ∞ :=
  if h : ∃ n : ℕ, ¬ M.approx n x y then (Nat.find h : ℕ∞) else ⊤

/-- Auxiliary: in `ℕ∞` the order is determined by the naturals from below. -/
theorem le_of_forall_natCast_lt {a b : ℕ∞}
    (h : ∀ n : ℕ, (n : ℕ∞) < a → (n : ℕ∞) < b) : a ≤ b := by
  by_contra hcon
  push_neg at hcon
  have hbne : b ≠ ⊤ := by
    intro htop
    rw [htop] at hcon
    exact absurd hcon (not_lt_of_ge le_top)
  obtain ⟨k, rfl⟩ := WithTop.ne_top_iff_exists.mp hbne
  exact absurd (h k hcon) (lt_irrefl _)

/-- **Balls are refinement classes.** Two states are indistinguishable at
depth `n` exactly when the distinguishing depth is strictly greater than
`n`. -/
theorem approx_iff_lt_sep (n : ℕ) (x y : M.St) :
    M.approx n x y ↔ (n : ℕ∞) < M.sep x y := by
  unfold sep
  by_cases h : ∃ m : ℕ, ¬ M.approx m x y
  · rw [dif_pos h]
    rw [Nat.cast_lt]
    constructor
    · intro hn
      by_contra hle
      push_neg at hle
      exact (Nat.find_spec h) (approx_antitone hle hn)
    · intro hlt
      by_contra hn
      exact absurd (Nat.find_le hn) (not_le_of_gt hlt)
  · rw [dif_neg h]
    push_neg at h
    simp [h n]

/-- Indistinguishability is infinite depth. -/
theorem sep_eq_top_iff (x y : M.St) : M.sep x y = ⊤ ↔ M.Indist x y := by
  rw [indist_iff_forall_approx]
  constructor
  · intro htop n
    exact (approx_iff_lt_sep n x y).mpr (by rw [htop]; exact WithTop.coe_lt_top n)
  · intro hall
    unfold sep
    rw [dif_neg]
    push_neg
    exact hall

@[simp] theorem sep_self (x : M.St) : M.sep x x = ⊤ :=
  (sep_eq_top_iff x x).mpr (indist_refl x)

theorem sep_comm (x y : M.St) : M.sep x y = M.sep y x := by
  apply le_antisymm <;>
    · apply le_of_forall_natCast_lt
      intro n hn
      exact (approx_iff_lt_sep n _ _).mp (approx_symm n ((approx_iff_lt_sep n _ _).mpr hn))

/-- Depth zero means the difference is already in the immediate response. -/
theorem sep_eq_zero_iff (x y : M.St) : M.sep x y = 0 ↔ M.R x ≠ M.R y := by
  constructor
  · intro h0 hR
    have : ¬ ((0 : ℕ) : ℕ∞) < M.sep x y := by rw [h0]; exact lt_irrefl _
    exact this ((approx_iff_lt_sep 0 x y).mp hR)
  · intro hR
    by_contra hne
    have hpos : (0 : ℕ∞) < M.sep x y := lt_of_le_of_ne (zero_le _) (Ne.symm hne)
    exact hR ((approx_iff_lt_sep 0 x y).mpr (by exact_mod_cast hpos))

/-- **The strong triangle inequality.** Distinguishing depth is an
ultrametric: `x` and `z` cannot be separated earlier than at least one of
the pairs
`(x,y)`, `(y,z)`. -/
theorem sep_ultrametric (x y z : M.St) :
    min (M.sep x y) (M.sep y z) ≤ M.sep x z := by
  apply le_of_forall_natCast_lt
  intro n hn
  rw [lt_min_iff] at hn
  exact (approx_iff_lt_sep n x z).mp
    (approx_trans n ((approx_iff_lt_sep n x y).mpr hn.1)
      ((approx_iff_lt_sep n y z).mpr hn.2))

/-- **Transport is Lipschitz.** A contextual transport decreases the
distinguishing depth by at most one step — a factor of 2 on the real
scale. -/
theorem sep_le_sep_transport_succ (a : M.Act) (x y : M.St) :
    M.sep x y ≤ M.sep (M.T a x) (M.T a y) + 1 := by
  apply le_of_forall_natCast_lt
  intro n hn
  have happ : M.approx n x y := (approx_iff_lt_sep n x y).mpr hn
  cases n with
  | zero =>
      have h1 : (0 : ℕ∞) < 1 := by norm_num
      have h2 : (1 : ℕ∞) ≤ M.sep (M.T a x) (M.T a y) + 1 := le_add_self
      simpa using lt_of_lt_of_le h1 h2
  | succ m =>
      have hm : M.approx m (M.T a x) (M.T a y) := happ.2 a
      have hlt : (m : ℕ∞) < M.sep (M.T a x) (M.T a y) :=
        (approx_iff_lt_sep m _ _).mp hm
      rcases eq_or_ne (M.sep (M.T a x) (M.T a y)) ⊤ with htop | hne
      · rw [htop]; simp
      · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
        rw [← hk] at hlt ⊢
        have hmk : m < k := Nat.cast_lt.mp hlt
        calc ((m + 1 : ℕ) : ℕ∞) < ((k + 1 : ℕ) : ℕ∞) := by
              exact_mod_cast Nat.succ_lt_succ hmk
          _ = (k : ℕ∞) + 1 := by push_cast; ring

/-! ### The filtration and the projective bonding map -/

/-- The depth-`n` equivalence as a `Setoid`. -/
def approxSetoid (M : Machine) (n : ℕ) : Setoid M.St :=
  ⟨M.approx n, ⟨approx_refl n, fun h => approx_symm n h, fun h₁ h₂ => approx_trans n h₁ h₂⟩⟩

/-- The depth-`n` quotient. -/
def Level (M : Machine) (n : ℕ) : Type _ := Quotient (M.approxSetoid n)

/-- **The projective bonding map.** A deeper quotient maps well onto a
shallower one: the filtration is nested. -/
def bond (M : Machine) (n : ℕ) : M.Level (n + 1) → M.Level n :=
  Quotient.lift (fun s => Quotient.mk (M.approxSetoid n) s)
    (fun _ _ h => Quotient.sound (approx_succ_le n h))

@[simp] theorem bond_mk (n : ℕ) (s : M.St) :
    M.bond n (Quotient.mk (M.approxSetoid (n + 1)) s)
      = Quotient.mk (M.approxSetoid n) s := rfl

theorem bond_surjective (n : ℕ) : Function.Surjective (M.bond n) := by
  intro q
  induction q using Quotient.inductionOn with
  | h s => exact ⟨Quotient.mk (M.approxSetoid (n + 1)) s, rfl⟩

/-! ### The real scale

`d_ASC = 2^{-sep}` is exactly the quantity computed by `distance_matrix` in
`worldmeta/topology.py`. It is secondary: all the content is already proved
at the level of depths. -/

/-- Translation of depth into the real scale. -/
noncomputable def dOf : ℕ∞ → ℝ
  | ⊤ => 0
  | (n : ℕ) => (2 : ℝ) ^ (-(n : ℤ))

@[simp] theorem dOf_top : dOf ⊤ = 0 := rfl

@[simp] theorem dOf_coe (n : ℕ) : dOf (n : ℕ∞) = (2 : ℝ) ^ (-(n : ℤ)) := rfl

theorem dOf_nonneg (a : ℕ∞) : 0 ≤ dOf a := by
  cases a with
  | top => simp
  | coe n => simpa using le_of_lt (zpow_pos (by norm_num : (0:ℝ) < 2) _)

/-- The scale decreases with depth: the later states separate, the closer they are. -/
theorem dOf_antitone : Antitone dOf := by
  intro a b hab
  cases b with
  | top => simpa using dOf_nonneg a
  | coe n =>
      cases a with
      | top => exact absurd hab (by simp)
      | coe m =>
          have hmn : m ≤ n := by exact_mod_cast hab
          simp only [dOf_coe]
          apply zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2)
          omega

theorem dOf_min (a b : ℕ∞) : dOf (min a b) = max (dOf a) (dOf b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (dOf_antitone h)]
  · rw [min_eq_right h, max_eq_right (dOf_antitone h)]

/-- The continuation distance. -/
noncomputable def dASC (M : Machine) (x y : M.St) : ℝ := dOf (M.sep x y)

theorem dASC_nonneg (x y : M.St) : 0 ≤ M.dASC x y := dOf_nonneg _

theorem dASC_comm (x y : M.St) : M.dASC x y = M.dASC y x := by
  unfold dASC; rw [sep_comm]

/-- Zero distance is exactly semantic identity. -/
theorem dASC_eq_zero_iff (x y : M.St) : M.dASC x y = 0 ↔ M.Indist x y := by
  rw [← sep_eq_top_iff]
  unfold dASC
  cases h : M.sep x y with
  | top => simp
  | coe n =>
      simp only [dOf_coe]
      constructor
      · intro hz
        exact absurd hz (ne_of_gt (zpow_pos (by norm_num : (0:ℝ) < 2) _))
      · intro hc; exact absurd hc (by simp)

/-- Distance one means the difference is already in the immediate response.
This fixes the depth convention of v0.18: `dep = 0` gives `d = 1`. -/
theorem dASC_eq_one_iff (x y : M.St) : M.dASC x y = 1 ↔ M.R x ≠ M.R y := by
  rw [← sep_eq_zero_iff]
  unfold dASC
  cases hs : M.sep x y with
  | top => simp
  | coe n =>
      simp only [dOf_coe]
      rw [show (1:ℝ) = (2:ℝ) ^ (0:ℤ) by norm_num,
        zpow_right_inj₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)]
      constructor
      · intro h
        have : n = 0 := by omega
        simp [this]
      · intro h
        have : n = 0 := by exact_mod_cast h
        omega

/-- **The ultrametric on the real scale.** A corollary of the depth theorem. -/
theorem dASC_ultrametric (x y z : M.St) :
    M.dASC x z ≤ max (M.dASC x y) (M.dASC y z) := by
  unfold dASC
  rw [← dOf_min]
  exact dOf_antitone (sep_ultrametric x y z)

end Machine

end MetaLang
