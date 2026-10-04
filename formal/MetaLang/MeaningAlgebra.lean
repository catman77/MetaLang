import MetaLang.ASCTopology

/-!
# The meaning algebra: signature and ASC continuity (v0.22 §1, §5, §8)

The book (`Meaning/formal/Shaman/meaning_algebra.lean`) supplies
`MeaningAlgebraData` with total `oplus`, `ominus`, `rho` and proves **only**
closure and compatibility with materialization. There is no associativity,
no commutativity, no identity and no cancellation there — deliberately so.

ASC adds two layers the book does not have:

* **descent** — when local operations glue into a global one
  (`AlgebraicDescent.lean`);
* **filtration compatibility** — when a global operation is continuous in
  the continuation topology (this file).

The central theorem: an operation preserving every relation `approx n` is
1-Lipschitz for the max ultrametric on the product:

  `dASC (op x y) (op x' y') ≤ max (dASC x x') (dASC y y')`.

The second result of the file is the **three independent requirements**
(v0.22 §8): closure, descent compatibility and filtration compatibility do
not follow from one another in the direction that matters. Both
countermodels are finite.
-/

namespace MetaLang

universe u

/-! ## The book layer: closure without laws -/

/-- A restatement of `MeaningAlgebraData` from `Meaning/formal/Shaman`. The
original cannot be imported: that project is pinned to toolchain `v4.28.0`,
this one to `v4.29.0-rc8`. Closure of the operations is automatic in Lean —
it is expressed by the totality of `α → α → α` itself; the book's one
substantive field is that `rho` preserves coherence. -/
structure BookAlgebra (α : Type u) where
  oplus : α → α → α
  ominus : α → α → α
  rho : α → α
  Coherent : α → α → Prop
  rho_preserves_coherence : ∀ s : α, Coherent s (rho s)

namespace BookAlgebra

/-- A witness that the book layer **imposes no law at all**: there is a
`BookAlgebra` whose `⊕` is neither associative nor commutative and has no
identity element — with the coherence condition fully satisfied. This is
exactly the boundary declared in v0.22 §1. -/
theorem book_layer_does_not_force_laws :
    ∃ A : BookAlgebra (Fin 3),
      (∀ s, A.Coherent s (A.rho s)) ∧
      ¬ (∀ x y z, A.oplus (A.oplus x y) z = A.oplus x (A.oplus y z)) ∧
      ¬ (∀ x y, A.oplus x y = A.oplus y x) ∧
      ¬ (∃ e, ∀ x, A.oplus e x = x ∧ A.oplus x e = x) := by
  refine ⟨⟨fun x _ => x + 1, fun x _ => x - 1, fun x => x, fun _ _ => True,
    fun _ => trivial⟩, fun _ => trivial, ?_, ?_, ?_⟩
  · intro h; have := h 0 0 0; revert this; decide
  · intro h; have := h 0 1; revert this; decide
  · rintro ⟨e, he⟩; revert he; revert e; decide

end BookAlgebra

namespace Machine

open scoped Classical

variable {M : Machine}

/-! ## The three requirements

Requirement (1) — closure — is automatic in Lean: every total
`op : M.St → M.St → M.St` is closed. The substantive ones are (2) and
(3). -/

/-- **Requirement (2): descent compatibility.** The operation is well
defined on the semantic quotient `M.St / Indist`. -/
def DescentCompat₂ (M : Machine) (op : M.St → M.St → M.St) : Prop :=
  ∀ x x' y y' : M.St, M.Indist x x' → M.Indist y y' → M.Indist (op x y) (op x' y')

/-- The unary form of requirement (2). -/
def DescentCompat₁ (M : Machine) (r : M.St → M.St) : Prop :=
  ∀ x y : M.St, M.Indist x y → M.Indist (r x) (r y)

/-- **Requirement (3): filtration compatibility.** Agreement of the inputs
up to semantic depth `n` implies agreement of the outputs up to the same
depth. -/
def FiltrationCompat₂ (M : Machine) (op : M.St → M.St → M.St) : Prop :=
  ∀ (n : ℕ) (x x' y y' : M.St),
    M.approx n x x' → M.approx n y y' → M.approx n (op x y) (op x' y')

/-- The unary form of requirement (3). -/
def FiltrationCompat₁ (M : Machine) (r : M.St → M.St) : Prop :=
  ∀ (n : ℕ) (x y : M.St), M.approx n x y → M.approx n (r x) (r y)

/-- (3) ⇒ (2): filtration compatibility is stronger than descent
compatibility, because indistinguishability is the intersection of all
`approx n`. -/
theorem descentCompat₂_of_filtrationCompat₂ {op : M.St → M.St → M.St}
    (h : M.FiltrationCompat₂ op) : M.DescentCompat₂ op := by
  intro x x' y y' hx hy
  exact indist_of_forall_approx fun n =>
    h n x x' y y' (approx_of_indist n hx) (approx_of_indist n hy)

theorem descentCompat₁_of_filtrationCompat₁ {r : M.St → M.St}
    (h : M.FiltrationCompat₁ r) : M.DescentCompat₁ r := by
  intro x y hx
  exact indist_of_forall_approx fun n => h n x y (approx_of_indist n hx)

/-! ## The ASC continuity theorem (v0.22 §5) -/

/-- The distinguishing depth of the output is at least the minimum of the
input depths. This is the `ℕ∞` form of continuity, free of real
arithmetic. -/
theorem min_sep_le_sep_op {op : M.St → M.St → M.St}
    (h : M.FiltrationCompat₂ op) (x x' y y' : M.St) :
    min (M.sep x x') (M.sep y y') ≤ M.sep (op x y) (op x' y') := by
  apply le_of_forall_natCast_lt
  intro n hn
  rw [lt_min_iff] at hn
  exact (approx_iff_lt_sep n _ _).mp
    (h n x x' y y' ((approx_iff_lt_sep n x x').mpr hn.1)
      ((approx_iff_lt_sep n y y').mpr hn.2))

/-- **The ASC continuity theorem.** A binary operation preserving every
level of the filtration is 1-Lipschitz for the max ultrametric on the
product — and therefore continuous in the ASC topology. -/
theorem dASC_op_le_max {op : M.St → M.St → M.St}
    (h : M.FiltrationCompat₂ op) (x x' y y' : M.St) :
    M.dASC (op x y) (op x' y') ≤ max (M.dASC x x') (M.dASC y y') := by
  have hmin := dOf_antitone (min_sep_le_sep_op h x x' y y')
  rw [dOf_min] at hmin
  exact hmin

theorem sep_le_sep_unary {r : M.St → M.St}
    (h : M.FiltrationCompat₁ r) (x y : M.St) :
    M.sep x y ≤ M.sep (r x) (r y) := by
  apply le_of_forall_natCast_lt
  intro n hn
  exact (approx_iff_lt_sep n _ _).mp (h n x y ((approx_iff_lt_sep n x y).mpr hn))

/-- The unary analogue: `rho` is 1-Lipschitz. -/
theorem dASC_unary_le {r : M.St → M.St}
    (h : M.FiltrationCompat₁ r) (x y : M.St) :
    M.dASC (r x) (r y) ≤ M.dASC x y :=
  dOf_antitone (sep_le_sep_unary h x y)

end Machine

/-! ## Separating the requirements: two finite countermodels -/

namespace Separation

/-- A machine with the identity transition: indistinguishability coincides
with equality of responses, so the semantic quotient is strictly coarser
than the state set. The states `0` and `1` are indistinguishable, `2` is
separated. -/
abbrev flatMachine : Machine.{0} where
  St := Fin 3
  Act := Unit
  Resp := Bool
  T := fun _ s => s
  R := fun s => s = 2

theorem flat_transport (w : List Unit) (s : Fin 3) :
    flatMachine.transport w s = s := by
  induction w generalizing s with
  | nil => rfl
  | cons _ w ih => simpa using ih s

theorem flat_indist_zero_one : flatMachine.Indist 0 1 := by
  intro w
  simp [flat_transport]

/-- An operation that separates the indistinguishable: `0 ↦ 2`, everything else `↦ 0`. -/
def badOp : Fin 3 → Fin 3 → Fin 3 := fun x _ => if x = 0 then 2 else 0

/-- **Separation (1) ⇏ (2).** A total — hence closed — operation need not be
well defined on the semantic quotient: it sends an indistinguishable pair to
a distinguishable one. -/
theorem closure_does_not_imply_descent :
    ¬ flatMachine.DescentCompat₂ badOp := by
  intro h
  have := h 0 1 0 0 flat_indist_zero_one (flatMachine.indist_refl 0)
  exact absurd (Machine.indist_resp this) (by decide)

/-- A machine in which all states are semantically distinct, yet the pair
`0, 1` agrees on the immediate response. Transitions: `0 ↦ 2`, `1 ↦ 3`,
`2 ↦ 2`, `3 ↦ 0`. -/
abbrev depthMachine : Machine.{0} where
  St := Fin 4
  Act := Unit
  Resp := Bool
  T := fun _ s => if s = 0 then 2 else if s = 1 then 3 else if s = 2 then 2 else 0
  R := fun s => s = 2

/-- All states are pairwise separated by a word of length ≤ 2, so the
semantic quotient of `depthMachine` is trivial and requirement (2) holds for
**every** total operation. -/
theorem depth_indist_eq {x y : Fin 4} (h : depthMachine.Indist x y) : x = y := by
  fin_cases x <;> fin_cases y <;>
    first
      | rfl
      | (exact absurd (h []) (by decide))
      | (exact absurd (h [()]) (by decide))
      | (exact absurd (h [(), ()]) (by decide))

theorem depth_descentCompat (op : Fin 4 → Fin 4 → Fin 4) :
    depthMachine.DescentCompat₂ op := by
  intro x x' y y' hx hy
  rw [depth_indist_eq hx, depth_indist_eq hy]
  exact depthMachine.indist_refl _

/-- An operation compatible with equality — and hence with descent — but
breaking the filtration already at depth `0`: `0 ↦ 2` (response `true`),
`1 ↦ 0` (response `false`), even though `approx 0 0 1`. -/
def coarseOp : Fin 4 → Fin 4 → Fin 4 := fun x _ => if x = 0 then 2 else 0

theorem depth_approx_zero : depthMachine.approx 0 0 1 :=
  (Machine.approx_zero_iff _ _).mpr rfl

/-- **Separation (1)+(2) ⇏ (3)** — gate `S14` of v0.22. The operation is
total and well defined on the semantic quotient, yet **not** ASC-continuous:
inputs agreeing up to depth `0` give outputs that already differ in the
immediate response. -/
theorem descent_does_not_imply_continuity :
    depthMachine.DescentCompat₂ coarseOp ∧ ¬ depthMachine.FiltrationCompat₂ coarseOp := by
  refine ⟨depth_descentCompat coarseOp, ?_⟩
  intro h
  have h0 := h 0 0 1 0 0 depth_approx_zero (depthMachine.approx_refl 0 0)
  exact absurd ((Machine.approx_zero_iff _ _).mp h0) (by decide)

/-- A break on the depth scale: the minimum of the input depths is not
dominated by the distinguishing depth of the outputs. This directly negates
the conclusion of `min_sep_le_sep_op`. -/
theorem coarse_breaks_depth_bound :
    ¬ min (depthMachine.sep 0 1) (depthMachine.sep (0 : Fin 4) 0) ≤
        depthMachine.sep (coarseOp 0 0) (coarseOp 1 0) := by
  have htop : depthMachine.sep (0 : Fin 4) 0 = ⊤ :=
    (Machine.sep_eq_top_iff _ _).mpr (depthMachine.indist_refl 0)
  have hout : depthMachine.sep (coarseOp 0 0) (coarseOp 1 0) = 0 :=
    (Machine.sep_eq_zero_iff _ _).mpr (by decide)
  have hlt : (0 : ℕ∞) < depthMachine.sep 0 1 := by
    have h := (Machine.approx_iff_lt_sep (M := depthMachine) 0 0 1).mp depth_approx_zero
    simpa using h
  rw [htop, hout, min_eq_left le_top]
  intro hle
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl 0)

/-- The real-valued form of the same break: the distance between the outputs
is maximal even though the inputs agree on the immediate response. -/
theorem coarse_output_distance_one :
    depthMachine.dASC (coarseOp 0 0) (coarseOp 1 0) = 1 := by
  rw [Machine.dASC_eq_one_iff]
  decide

end Separation

end MetaLang
