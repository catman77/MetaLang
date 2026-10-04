import MetaLang.MeaningAlgebra
import MetaLang.Descent

/-!
# Descent of meaning operations (v0.22 §2–§4, v0.23 §2–§5)

Two **different** constructions, which v0.23 §3 insists must not be
conflated.

* **The atlas of full presentations** (v0.22). Each chart is a full copy of
  the semantic space, differing only by gauge. Then any pair of operands
  lives in a single chart, and compatibility on overlaps yields unique
  global operations for which every chart map is a homomorphism.
* **The product atlas** (v0.23). Charts are partial, the output of a local
  operation may lie outside both operand charts, and the operation lives not
  over a cover of `Q` but over a cover of `Q × Q`. This is exactly the
  tuple-coverage condition that v0.22 skipped.

The third strand of the file is **transport of equations**: a term language
for the signature and the lemma that a homomorphism commutes with term
evaluation. Hence v0.22 §4: ASC transports exactly the laws present in the
source and creates no new ones.
-/

namespace MetaLang

universe u v w

/-! ## The meaning signature and homomorphisms -/

/-- The book's signature without the coherence condition: three operation symbols. -/
structure Sig (α : Type u) where
  oplus : α → α → α
  ominus : α → α → α
  rho : α → α

/-- A homomorphism of the signature. -/
def Sig.Hom {α : Type u} {β : Type v} (A : Sig α) (B : Sig β) (f : α → β) : Prop :=
  (∀ x y, f (A.oplus x y) = B.oplus (f x) (f y)) ∧
  (∀ x y, f (A.ominus x y) = B.ominus (f x) (f y)) ∧
  (∀ x, f (A.rho x) = B.rho (f x))

/-! ## The atlas of full presentations (v0.22 §2–§3) -/

/-- An algebraic atlas: a family of full presentations `pres i : C i ↠ Q`,
local operations in every chart, and compatibility on overlaps. The
condition `pres_surj` is exactly the "full presentation" of v0.22 §1; tuple
coverage follows from it automatically. -/
structure AlgAtlas (Q : Type u) where
  ι : Type u
  nonempty : Nonempty ι
  C : ι → Type u
  pres : ∀ i, C i → Q
  pres_surj : ∀ i, Function.Surjective (pres i)
  local_sig : ∀ i, Sig (C i)
  /-- Compatibility: if two charts present the same operands, they present
  the same result too. This is the descent condition of v0.22 §2. -/
  compat_oplus : ∀ i j (a b : C i) (a' b' : C j),
    pres i a = pres j a' → pres i b = pres j b' →
    pres i ((local_sig i).oplus a b) = pres j ((local_sig j).oplus a' b')
  compat_ominus : ∀ i j (a b : C i) (a' b' : C j),
    pres i a = pres j a' → pres i b = pres j b' →
    pres i ((local_sig i).ominus a b) = pres j ((local_sig j).ominus a' b')
  compat_rho : ∀ i j (a : C i) (a' : C j),
    pres i a = pres j a' →
    pres i ((local_sig i).rho a) = pres j ((local_sig j).rho a')

namespace AlgAtlas

variable {Q : Type u} (A : AlgAtlas Q)

open scoped Classical

/-- An arbitrarily chosen base chart. -/
noncomputable def base : A.ι := Classical.choice A.nonempty

/-- Lifting a point of `Q` into the base chart. -/
noncomputable def lift (q : Q) : A.C A.base :=
  Classical.choose (A.pres_surj A.base q)

@[simp] theorem pres_lift (q : Q) : A.pres A.base (A.lift q) = q :=
  Classical.choose_spec (A.pres_surj A.base q)

/-- The global operations on `Q`, built through the base chart. -/
noncomputable def global : Sig Q where
  oplus := fun x y => A.pres A.base ((A.local_sig A.base).oplus (A.lift x) (A.lift y))
  ominus := fun x y => A.pres A.base ((A.local_sig A.base).ominus (A.lift x) (A.lift y))
  rho := fun x => A.pres A.base ((A.local_sig A.base).rho (A.lift x))

/-- **The algebraic descent theorem (v0.22 §3).** Every chart map of the
atlas is a homomorphism into the global algebra. Compatibility on overlaps
is exactly what totality and closure in each chart lack. -/
theorem pres_hom (i : A.ι) : (A.local_sig i).Hom A.global (A.pres i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    exact A.compat_oplus i A.base a b _ _ (by simp) (by simp)
  · intro a b
    exact A.compat_ominus i A.base a b _ _ (by simp) (by simp)
  · intro a
    exact A.compat_rho i A.base a _ (by simp)

/-- **Uniqueness of the global operations.** Any signature on `Q` for which
all chart maps are homomorphisms coincides with `global`. -/
theorem global_unique (B : Sig Q) (hB : ∀ i, (A.local_sig i).Hom B (A.pres i)) :
    B = A.global := by
  obtain ⟨bo, bm, br⟩ := B
  have hb := hB A.base
  have h1 : bo = A.global.oplus := by
    funext x y
    have := hb.1 (A.lift x) (A.lift y)
    simpa [global] using this.symm
  have h2 : bm = A.global.ominus := by
    funext x y
    have := hb.2.1 (A.lift x) (A.lift y)
    simpa [global] using this.symm
  have h3 : br = A.global.rho := by
    funext x
    have := hb.2.2 (A.lift x)
    simpa [global] using this.symm
  rw [h1, h2, h3]

/-- **The cocycle law holds automatically** for full presentations. The
transition `g i j` is defined as "lift through `j` what `i` presents"; at the
level of presentations the triple overlap is an identity. -/
theorem cocycle (i j k : A.ι) (a : A.C i) (b : A.C j) (c : A.C k)
    (hij : A.pres i a = A.pres j b) (hjk : A.pres j b = A.pres k c) :
    A.pres i a = A.pres k c := hij.trans hjk

end AlgAtlas

/-! ## Countermodel: closure in the charts is not enough (v0.22 `S15`, `S16`) -/

namespace NoDescent

/-- Two gauges on the same carrier `Bool`: the identity and the inverting
one. The local operation in both is conjunction; both are total and
closed. -/
def opAnd : Bool → Bool → Bool := fun a b => a && b

/-- **Totality and closure in every chart do not give descent.** There is no
global operation compatible with both gauges: one and the same local table,
read under different presentations, demands incompatible values. The symbol
names agree — that is not enough. -/
theorem closure_without_compat_has_no_global :
    ¬ ∃ μ : Bool → Bool → Bool,
        (∀ a b, μ a b = opAnd a b) ∧
        (∀ a b, μ (!a) (!b) = !(opAnd a b)) := by
  rintro ⟨μ, h1, h2⟩
  have e1 := h1 false true
  have e2 := h2 true false
  simp [opAnd] at e1 e2
  rw [e1] at e2
  exact Bool.noConfusion e2

end NoDescent

/-! ## The term language and transport of equations (v0.22 §4) -/

/-- A term of the meaning signature over a variable set `V`. -/
inductive Term (V : Type u) where
  | var : V → Term V
  | oplus : Term V → Term V → Term V
  | ominus : Term V → Term V → Term V
  | rho : Term V → Term V
  deriving Inhabited

namespace Term

/-- Evaluation of a term in an algebra under a given substitution. -/
def eval {V : Type u} {α : Type v} (A : Sig α) (σ : V → α) : Term V → α
  | .var x => σ x
  | .oplus t u => A.oplus (eval A σ t) (eval A σ u)
  | .ominus t u => A.ominus (eval A σ t) (eval A σ u)
  | .rho t => A.rho (eval A σ t)

/-- **A homomorphism commutes with the evaluation of every term.** -/
theorem eval_hom {V : Type u} {α : Type v} {β : Type w}
    {A : Sig α} {B : Sig β} {f : α → β} (h : A.Hom B f) (σ : V → α) :
    ∀ t : Term V, f (eval A σ t) = eval B (f ∘ σ) t := by
  intro t
  induction t with
  | var x => rfl
  | oplus t u iht ihu => simp [eval, h.1, iht, ihu]
  | ominus t u iht ihu => simp [eval, h.2.1, iht, ihu]
  | rho t iht => simp [eval, h.2.2, iht]

end Term

open scoped Classical in
/-- **Transport of equations (v0.22 §4, gate `S17`).** If the equation
`t = u` holds in the local algebra and the presentation is surjective, it
holds in the global one. ASC transports the source's laws — and only
those. -/
theorem law_descends {V : Type u} {α : Type v} {β : Type v}
    {A : Sig α} {B : Sig β} {f : α → β}
    (h : A.Hom B f) (hf : Function.Surjective f) {t u : Term V}
    (hlaw : ∀ σ : V → α, Term.eval A σ t = Term.eval A σ u) :
    ∀ τ : V → β, Term.eval B τ t = Term.eval B τ u := by
  intro τ
  have hσ : ∃ σ : V → α, f ∘ σ = τ := by
    refine ⟨fun x => Classical.choose (hf (τ x)), ?_⟩
    funext x
    exact Classical.choose_spec (hf (τ x))
  obtain ⟨σ, hστ⟩ := hσ
  have ht := Term.eval_hom h σ t
  have hu := Term.eval_hom h σ u
  rw [hστ] at ht hu
  rw [← ht, ← hu, hlaw σ]

/-- **Transport of equations through an atlas (v0.22 §4).** Every equation
of the signature that holds in one chart holds in the global algebra: the
presentation is surjective and is a homomorphism. The converse fails — see
`MeaningWitnesses.lean`. -/
theorem AlgAtlas.law_descends {Q : Type u} (A : AlgAtlas Q) (i : A.ι)
    {V : Type u} {t u : Term V}
    (hlaw : ∀ σ : V → A.C i,
      Term.eval (A.local_sig i) σ t = Term.eval (A.local_sig i) σ u) :
    ∀ τ : V → Q, Term.eval A.global τ t = Term.eval A.global τ u :=
  _root_.MetaLang.law_descends (A.pres_hom i) (A.pres_surj i) hlaw

/-! ## The product atlas (v0.23 §2–§5) -/

/-- A product atlas: charts are partial, the local map is defined on
selected cells of a cover of `Q × Q`, and it takes values in `Q` (after
semantic descent of the output). -/
structure ProductAtlas (Q : Type u) where
  ι : Type u
  chart : ι → Set Q
  cell : ι → ι → Prop
  mu : ι → ι → Q → Q → Q
  /-- Tuple coverage: every pair lies in at least one cell. This is exactly
  the condition v0.22 got for free and v0.23 must demand. -/
  tuple_cover : ∀ x y : Q, ∃ i j, cell i j ∧ x ∈ chart i ∧ y ∈ chart j
  /-- Compatibility on the overlap of cells. -/
  overlap : ∀ i j i' j' (x y : Q), cell i j → cell i' j' →
    x ∈ chart i → y ∈ chart j → x ∈ chart i' → y ∈ chart j' →
    mu i j x y = mu i' j' x y

namespace ProductAtlas

variable {Q : Type u} (P : ProductAtlas Q)

open scoped Classical

/-- The global operation glued from the local ones. -/
noncomputable def glue (x y : Q) : Q :=
  P.mu (Classical.choose (P.tuple_cover x y))
    (Classical.choose (Classical.choose_spec (P.tuple_cover x y))) x y

theorem glue_spec (x y : Q) :
    ∃ i j, P.cell i j ∧ x ∈ P.chart i ∧ y ∈ P.chart j ∧ P.glue x y = P.mu i j x y := by
  refine ⟨Classical.choose (P.tuple_cover x y),
    Classical.choose (Classical.choose_spec (P.tuple_cover x y)), ?_, ?_, ?_, rfl⟩
  · exact (Classical.choose_spec (Classical.choose_spec (P.tuple_cover x y))).1
  · exact (Classical.choose_spec (Classical.choose_spec (P.tuple_cover x y))).2.1
  · exact (Classical.choose_spec (Classical.choose_spec (P.tuple_cover x y))).2.2

/-- **The product descent theorem (v0.23 §2).** The gluing agrees with every
local map on its own cell. -/
theorem glue_eq_local (i j : P.ι) (x y : Q)
    (hc : P.cell i j) (hx : x ∈ P.chart i) (hy : y ∈ P.chart j) :
    P.glue x y = P.mu i j x y := by
  obtain ⟨i', j', hc', hx', hy', heq⟩ := P.glue_spec x y
  rw [heq]
  exact P.overlap i' j' i j x y hc' hc hx' hy' hx hy

/-- **Uniqueness of the global operation.** -/
theorem glue_unique (μ : Q → Q → Q)
    (hμ : ∀ i j x y, P.cell i j → x ∈ P.chart i → y ∈ P.chart j → μ x y = P.mu i j x y) :
    μ = P.glue := by
  funext x y
  obtain ⟨i, j, hc, hx, hy, heq⟩ := P.glue_spec x y
  rw [hμ i j x y hc hx hy, heq]

end ProductAtlas

/-! ## Descent of a unary operation over a cover of states (v0.23 `S9`) -/

/-- A unary operation lives over a cover of `Q` itself rather than of its
square: for it the tuple-coverage condition degenerates to an ordinary
cover. -/
structure UnaryAtlas (Q : Type u) where
  ι : Type u
  chart : ι → Set Q
  covers : ∀ x : Q, ∃ i, x ∈ chart i
  r : ι → Q → Q
  overlap : ∀ i j (x : Q), x ∈ chart i → x ∈ chart j → r i x = r j x

namespace UnaryAtlas

variable {Q : Type u} (U : UnaryAtlas Q)

open scoped Classical

/-- The global unary operation glued from the local ones. -/
noncomputable def glue (x : Q) : Q := U.r (Classical.choose (U.covers x)) x

theorem glue_eq_local (i : U.ι) (x : Q) (hx : x ∈ U.chart i) : U.glue x = U.r i x := by
  have hmem := Classical.choose_spec (U.covers x)
  exact U.overlap _ i x hmem hx

/-- **`ρ` globalizes from a cover of states, and uniquely so.** -/
theorem glue_unique (ρ : Q → Q)
    (hρ : ∀ i x, x ∈ U.chart i → ρ x = U.r i x) : ρ = U.glue := by
  funext x
  obtain ⟨i, hi⟩ := U.covers x
  rw [hρ i x hi, U.glue_eq_local i x hi]

end UnaryAtlas

/-! ## Countermodels for the product atlas -/

namespace ProductCounter

/-- An atlas with three one-point charts on `Fin 3` and constant output `2`. -/
abbrev crossAtlas : ProductAtlas (Fin 3) where
  ι := Fin 3
  chart := fun i => {i}
  cell := fun _ _ => True
  mu := fun _ _ _ _ => 2
  tuple_cover := fun x y => ⟨x, y, trivial, rfl, rfl⟩
  overlap := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl

/-- **Charts are not subalgebras (v0.23 §4, gate `S16`).** The output of the
local operation lies outside both operand charts; closure belongs to the
global `Q`, not to each chart. -/
theorem output_leaves_charts :
    crossAtlas.mu 0 1 0 1 ∉ crossAtlas.chart 0 ∧
    crossAtlas.mu 0 1 0 1 ∉ crossAtlas.chart 1 := by
  constructor <;> · intro h; exact absurd h (by decide)

/-- **Corrupting a single overlap breaks well-definedness (v0.23, gate
`S14`).** Two cells cover the same pair but give different values — no global
operation agreeing with both exists. -/
theorem corrupt_overlap_no_global :
    ¬ ∃ μ : Bool → Bool → Bool,
        (∀ x y, μ x y = (x && y)) ∧ (∀ x y, μ x y = (x || y)) := by
  rintro ⟨μ, h1, h2⟩
  have e1 := h1 true false
  have e2 := h2 true false
  rw [e1] at e2
  exact Bool.noConfusion e2

end ProductCounter

/-! ## Bridge to ASC continuity (v0.23 §6, filtration form) -/

/-- The glued operation is continuous in the ASC topology as soon as it
preserves every level of the filtration. This composes the product descent
theorem with the ASC continuity theorem of `MeaningAlgebra.lean`; the
topological gluing lemma (v0.23 §6, first half) is not formalized — see §3
of `PRD_M8.md`. -/
theorem glue_continuous {M : Machine} (P : ProductAtlas M.St)
    (h : M.FiltrationCompat₂ P.glue) (x x' y y' : M.St) :
    M.dASC (P.glue x y) (P.glue x' y') ≤ max (M.dASC x x') (M.dASC y y') :=
  Machine.dASC_op_le_max h x x' y y'

end MetaLang
