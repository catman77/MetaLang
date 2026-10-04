import Mathlib

/-!
# Typed self-reference (v0.31)

Self-referential admissibility is typed not as a Boolean oracle but as a
**set of branches**: an exact outcome is `A ⊆ B`, not a truth value.
Self-reference is a transformer `Φ : P(B) → P(B)`, and exact
self-consistency `A = Φ(A)` may have no solutions, one, or many.

The content of v0.31 in one sentence: **`Φ` is in general not monotone**, so
Knaster–Tarski does not apply to it. What is monotone is the interval
transformer — the best collecting abstraction over all exact outcomes inside
`[L, U]`. But its fixed point **is not** a truth value: it may fail to be a
singleton, and it may exist where there are no exact solutions at all.
-/

namespace MetaLang

variable {B : Type} [Fintype B] [DecidableEq B]

/-- An interval of partial information: `lo` are the branches that are
definitely admissible, `hi` those that are possibly admissible. -/
@[ext]
structure Interval (B : Type) [Fintype B] [DecidableEq B] where
  /-- Lower bound: definitely admissible. -/
  lo : Finset B
  /-- Upper bound: possibly admissible. -/
  hi : Finset B

/-- Concretization of an interval: all exact outcomes inside it. -/
def gamma (I : Interval B) : Finset (Finset B) :=
  Finset.univ.filter (fun A => I.lo ⊆ A ∧ A ⊆ I.hi)

/-- The interval transformer — the best collecting abstraction of `Φ` on `[L, U]`. -/
def istep (Φ : Finset B → Finset B) (I : Interval B) : Interval B where
  lo := Finset.univ.filter (fun b => ∀ A ∈ gamma I, b ∈ Φ A)
  hi := Finset.univ.filter (fun b => ∃ A ∈ gamma I, b ∈ Φ A)

/-- **Monotonicity of the interval transformer.** A wider interval on the
input gives a wider interval on the output. It is `istep`, not `Φ`, to which
the fixed-point theorem applies. -/
theorem istep_mono (Φ : Finset B → Finset B) {I J : Interval B}
    (hsub : gamma I ⊆ gamma J) :
    (istep Φ J).lo ⊆ (istep Φ I).lo ∧ (istep Φ I).hi ⊆ (istep Φ J).hi := by
  constructor
  · intro b hb
    simp only [istep, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact fun A hA => hb A (hsub hA)
  · intro b hb
    simp only [istep, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    obtain ⟨A, hA, hbA⟩ := hb
    exact ⟨A, hsub hA, hbA⟩

/-! ### Exact self-consistency: zero, one or many solutions -/

/-- An exact fixed point. -/
def ExactFixed (Φ : Finset B → Finset B) (A : Finset B) : Prop := Φ A = A

instance (Φ : Finset B → Finset B) (A : Finset B) : Decidable (ExactFixed Φ A) := by
  unfold ExactFixed; infer_instance

/-- The liar: complementation. -/
def liar : Finset Bool → Finset Bool := fun A => Aᶜ

/-- The identity transformer. -/
def idPhi : Finset Bool → Finset Bool := fun A => A

/-- A constant transformer. -/
def constPhi : Finset Bool → Finset Bool := fun _ => {true}

/-- **Zero solutions.** The liar has no exact fixed point at all. -/
theorem liar_no_exact_fixed : ∀ A : Finset Bool, ¬ ExactFixed liar A := by decide

/-- **Many solutions.** The identity transformer has four. -/
theorem idPhi_all_fixed : ∀ A : Finset Bool, ExactFixed idPhi A := by decide

/-- **Exactly one solution.** -/
theorem constPhi_unique_fixed :
    ∀ A : Finset Bool, ExactFixed constPhi A ↔ A = {true} := by decide

/-- **`Φ` need not be monotone.** The liar is antitone, so Knaster–Tarski
does not apply to it — this is precisely the difficulty of v0.31. -/
theorem liar_not_monotone : ¬ Monotone liar := by
  intro hmono
  have h : (∅ : Finset Bool) ⊆ {true} := by decide
  have := hmono h
  revert this
  decide

/-! ### A partial fixed point is not truth -/

/-- The full interval: nothing is determined. -/
def fullInterval : Interval Bool := ⟨∅, Finset.univ⟩

/-- The full interval is a fixed point of the interval liar. -/
theorem liar_interval_fixed : istep liar fullInterval = fullInterval := by
  ext1
  · show (Finset.univ.filter (fun b => ∀ A ∈ gamma fullInterval, b ∈ liar A)) = ∅
    decide
  · show (Finset.univ.filter (fun b => ∃ A ∈ gamma fullInterval, b ∈ liar A)) = Finset.univ
    decide

/-- **The key theorem of v0.31.** There is a self-reference that has a
partial fixed point but **no** exact solution at all, and that partial point
is not a singleton. Identifying it with a truth value is forbidden. -/
theorem partial_fixed_point_is_not_truth :
    ∃ (Φ : Finset Bool → Finset Bool) (I : Interval Bool),
      istep Φ I = I ∧ (∀ A : Finset Bool, ¬ ExactFixed Φ A) ∧ I.lo ≠ I.hi :=
  ⟨liar, fullInterval, liar_interval_fixed, liar_no_exact_fixed, by decide⟩

/-- The concretization of that partial point contains all four outcomes:
the ignorance is maximal, not resolved in favour of one branch. -/
theorem liar_gamma_full : (gamma fullInterval).card = 4 := by decide

end MetaLang
