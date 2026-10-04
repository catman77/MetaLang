import Mathlib

/-!
# Theory space and the diagonalization boundary (v0.29–v0.30)

Two predicates on theory space are **different**:

* `Prov_T` — internal syntactic provability;
* `Adm_source` — external source admissibility of a theory extension.

Even when the internal status of a sentence is held fixed as unresolved, the
source grammar may allow 0, 1 or 2 admissible extensions. This does not
contradict incompleteness, because the source predicate is **not identified**
with `Prov_T` and is not assumed internally definable.

## The boundary that must not be crossed

The `FROZEN_PROTOCOL.md` files of v0.29 and v0.30 forbid deriving anything
about Gödel incompleteness from this: "A PASS does not establish, refute,
bypass, or weaken
Gödel incompleteness», «no claim that bounded search proves unprovability».
So exactly two things are formalized here: the **diagonal lemma** as a
fixed-point schema and the **Tarski barrier**. Incompleteness is not proved
and cannot be derived from this file.
-/

namespace MetaLang

/-! ### Theory space: `Prov` and `Adm` are different predicates

The four frozen source modes of v0.29/v0.30 and their branch profile. -/

namespace TheorySpace

/-- A branch: the positive or the negative extension of the theory. -/
abbrev Branch := Bool

/-- Source modes: bifurcation, resolution to plus, resolution to minus, blocked. -/
abbrev Mode := Fin 4

/-- Source admissibility of a branch in a given mode. -/
def adm : Mode → Branch → Bool
  | 0, _ => true
  | 1, b => b
  | 2, b => !b
  | _, _ => false

/-- Internal provability: both branches stay unresolved in every mode. This
is what "the status of `G_T` is held fixed" means. -/
def prov : Mode → Branch → Bool := fun _ _ => false

/-- The number of admissible extensions of the theory. -/
def branchCount (m : Mode) : Nat :=
  ([true, false].filter (fun b => adm m b)).length

/-- **The branch profile**: all three possibilities occur — 2, 1 and 0.
This matches the frozen expectation of v0.29/v0.30. -/
theorem branch_profile :
    branchCount 0 = 2 ∧ branchCount 1 = 1 ∧ branchCount 2 = 1 ∧ branchCount 3 = 0 := by
  decide

/-- **`Prov` and `Adm` are different predicates.** -/
theorem prov_ne_adm : ∃ (m : Mode) (b : Branch), prov m b ≠ adm m b :=
  ⟨0, true, by decide⟩

/-- **The key claim of v0.30 §2.** The internal status is held unresolved in
every mode, and still the number of source-admissible extensions takes the
values 2, 1 and 0. So provability and source admissibility are independent
axes. -/
theorem provability_fixed_admissibility_varies :
    (∀ (m : Mode) (b : Branch), prov m b = false) ∧
      branchCount 0 = 2 ∧ branchCount 1 = 1 ∧ branchCount 3 = 0 := by
  refine ⟨fun m b => rfl, ?_, ?_, ?_⟩ <;> decide

end TheorySpace

/-! ### The diagonal lemma

Arithmetized self-reference: with a representable substitution, for every
unary formula `φ` there is a sentence `G` identically equal to `φ(⌜G⌝)`.
This is a purely syntactic fixed point — exactly what the executable code of
v0.30 checks under many random Gödel codings. -/

/-- A coding system with representable substitution. -/
structure DiagonalSystem where
  /-- Sentences. -/
  Sent : Type
  /-- Unary formulas. -/
  Form : Type
  /-- Gödel numbering of sentences. -/
  code : Sent → ℕ
  /-- Substitution of a number into a formula. -/
  app : Form → ℕ → Sent
  /-- The diagonalization `β(x) := φ(Sub(x,x))`. -/
  diagonal : Form → Form
  /-- The code of the diagonalized formula itself. -/
  selfCode : Form → ℕ
  /-- Correctness of substitution: `Sub(b,b) = code(G)`. -/
  fixed : ∀ φ : Form,
    app (diagonal φ) (selfCode (diagonal φ))
      = app φ (code (app (diagonal φ) (selfCode (diagonal φ))))

namespace DiagonalSystem

variable (D : DiagonalSystem)

/-- **The diagonal lemma.** For every unary formula there is a sentence
identical to its own assertion about itself. -/
theorem diagonal_lemma (φ : D.Form) : ∃ G : D.Sent, G = D.app φ (D.code G) :=
  ⟨D.app (D.diagonal φ) (D.selfCode (D.diagonal φ)), D.fixed φ⟩

end DiagonalSystem

/-- A degenerate model: it shows that the axioms of `DiagonalSystem` are
consistent. It carries no substantive force. -/
def trivialDiagonal : DiagonalSystem where
  Sent := Unit
  Form := Unit
  code := fun _ => 0
  app := fun _ _ => ()
  diagonal := id
  selfCode := fun _ => 0
  fixed := fun _ => rfl

/-! ### The Tarski barrier

A predicate of the same language that totally and correctly expresses truth
for all sentences of that language is impossible. This is **not** Gödel's
incompleteness theorem, nor a way around it: it is the barrier to internal
definability of truth. -/

/-- **The Tarski barrier.** There is no total predicate of the same language
correctly expressing truth for all sentences of that language. -/
theorem no_total_truth_predicate (D : DiagonalSystem)
    (Truth : D.Sent → Prop)
    (A : D.Form)
    (neg : D.Form → D.Form)
    (hneg : ∀ (φ : D.Form) (n : ℕ), Truth (D.app (neg φ) n) ↔ ¬ Truth (D.app φ n))
    (hA : ∀ σ : D.Sent, Truth (D.app A (D.code σ)) ↔ Truth σ) :
    False := by
  obtain ⟨L, hL⟩ := D.diagonal_lemma (neg A)
  have e1 : Truth L ↔ Truth (D.app (neg A) (D.code L)) := by rw [← hL]
  have e2 := hneg A (D.code L)
  have e3 := hA L
  have hself : Truth L ↔ ¬ Truth L := e1.trans (e2.trans (not_congr e3))
  have hn : ¬ Truth L := fun h => hself.mp h h
  exact hn (hself.mpr hn)

end MetaLang
