import MetaLang.TheoryPresentation
import MetaLang.Projection

/-!
# The boundary object: two diagnostic layers (v0.32 §1–§2)

v0.31 provides a partial status — the interval `[L, U]`. v0.32 shows that
this is not enough: the interval does **not classify the cause** of
unresolvedness. Different transformers with one and the same fully unknown
interval are built differently, and what tells them apart is a second layer —
the **recurrent core** of a finite functional graph.

The boundary object is a pair of layers: the partial interval and the set of
points on nontrivial cycles. One-cycles are exactly the exact solutions;
cycles of length greater than one are explicit witnesses of an obstruction,
not truth values.

The five modes of §1 are formalized, and the pair "number of exact solutions,
presence of a nontrivial cycle" is proved to tell them apart pairwise,
whereas the partial layer coincides for some of them.

The second half of v0.32 — projection descent — is already settled in
`Projection.lean` (milestone M9); only the cross-references are added here.
-/

namespace MetaLang

namespace Boundary

open Partial

/-! ## The recurrent core -/

/-- A point lies on a cycle: it returns within one of the first four steps.
On a four-element carrier that is enough. -/
def IsCyclic (Φ : Finset Bool → Finset Bool) (A : Finset Bool) : Prop :=
  ∃ n : Fin 4, Φ^[(n : ℕ) + 1] A = A

instance (Φ : Finset Bool → Finset Bool) (A : Finset Bool) :
    Decidable (IsCyclic Φ A) := by
  unfold IsCyclic
  infer_instance

/-- Nontrivial recurrence: a cycle of length greater than one. -/
def HasNontrivialCycle (Φ : Finset Bool → Finset Bool) : Prop :=
  ∃ A : Finset Bool, IsCyclic Φ A ∧ Φ A ≠ A

instance (Φ : Finset Bool → Finset Bool) : Decidable (HasNontrivialCycle Φ) := by
  unfold HasNontrivialCycle
  infer_instance

/-- The number of exact solutions. -/
def fixCount (Φ : Finset Bool → Finset Bool) : ℕ :=
  (Finset.univ.filter (fun A : Finset Bool => Φ A = A)).card

/-- The number of points on nontrivial cycles. -/
def cycleCount (Φ : Finset Bool → Finset Bool) : ℕ :=
  (Finset.univ.filter (fun A : Finset Bool => IsCyclic Φ A ∧ Φ A ≠ A)).card

/-- The signature of the cause: how many solutions, and how many points on the obstruction. -/
def signature (Φ : Finset Bool → Finset Bool) : ℕ × ℕ := (fixCount Φ, cycleCount Φ)

/-- **The set of exact solutions is read off the one-cycles (gate `S28` of
v0.32).** It is not derived from the partial status but taken from the
recurrence layer. -/
theorem exact_iff_one_cycle (Φ : Finset Bool → Finset Bool) (A : Finset Bool) :
    ExactFixed Φ A ↔ (IsCyclic Φ A ∧ Φ A = A) := by
  constructor
  · intro h
    exact ⟨⟨0, by simpa using h⟩, h⟩
  · intro h
    exact h.2

/-- **Nontrivial cycles are witnesses of an obstruction, not truth values
(gate `S29` of v0.32).** A point on a long cycle is certainly not a
solution. -/
theorem cycle_not_solution {Φ : Finset Bool → Finset Bool} {A : Finset Bool}
    (h : IsCyclic Φ A) (hne : Φ A ≠ A) : ¬ ExactFixed Φ A := hne

/-! ## The five boundary modes -/

/-- A unique solution hidden by nontrivial recurrence. -/
def hiddenPhi : Finset Bool → Finset Bool := fun A =>
  if A = ∅ then {true} else if A = {true} then ∅ else Finset.univ

/-- **The liar: no solutions, yet the recurrence is nontrivial (gate `S3`).** -/
theorem liar_mode : signature liar = (0, 4) := by decide

/-- **The identity: four solutions and no nontrivial recurrence (gate
`S4`).** -/
theorem identity_mode : signature idPhi = (4, 0) := by decide

/-- **A unique solution can be hidden by recurrence (gate `S5`).** -/
theorem hidden_mode : signature hiddenPhi = (1, 2) := by decide

/-- **Several solutions coexist with an obstruction (gate `S6`).** -/
theorem bifurcated_mode : signature bifurcated = (2, 2) := by decide

/-- **Exact partial resolution (gate `S8`).** The constant transformer has
one solution and no recurrence. -/
theorem resolved_mode : signature constPhi = (1, 0) := by decide

/-- **The five frozen modes are classified exactly (gate `S2`).** The
signature "number of solutions, number of points on the obstruction" tells
them apart pairwise. -/
theorem five_modes_distinct :
    signature liar ≠ signature idPhi ∧
    signature liar ≠ signature hiddenPhi ∧
    signature liar ≠ signature bifurcated ∧
    signature liar ≠ signature constPhi ∧
    signature idPhi ≠ signature hiddenPhi ∧
    signature idPhi ≠ signature bifurcated ∧
    signature idPhi ≠ signature constPhi ∧
    signature hiddenPhi ≠ signature bifurcated ∧
    signature hiddenPhi ≠ signature constPhi ∧
    signature bifurcated ≠ signature constPhi := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

/-! ## The two layers are logically distinct -/

/-- **Total unknownness has several distinct cause signatures (gates `S12`,
`S15`, `S16` of v0.32).** The liar and the bifurcation give the same partial
interval but a different number of solutions: the obstruction layer does not
conflate "no solutions" with "many solutions". -/
theorem unknown_has_distinct_causes :
    istep liar fullInterval = istep bifurcated fullInterval ∧
    fixCount liar ≠ fixCount bifurcated := by
  refine ⟨?_, by decide⟩
  rw [liar_interval_fixed, bifurcated_interval_fixed]

/-- **The resolved mode already differs from total unknownness at the
partial layer (gate `S8`).** -/
theorem resolved_ne_unknown :
    istep constPhi fullInterval ≠ fullInterval := by
  intro h
  have hlo : (istep constPhi fullInterval).lo = (∅ : Finset Bool) := by
    rw [h]; rfl
  revert hlo
  decide

/-- **The boundary object carries both layers (gate `S1` of v0.32).** -/
structure BoundaryData where
  /-- The partial layer: the interval of v0.31. -/
  interval : Interval Bool
  /-- The recurrence layer: the points on nontrivial cycles. -/
  cycles : Finset (Finset Bool)
  /-- The exact solutions. -/
  fix : Finset (Finset Bool)

/-- The boundary object of a transformer. -/
def boundaryOf (Φ : Finset Bool → Finset Bool) : BoundaryData where
  interval := istep Φ fullInterval
  cycles := Finset.univ.filter (fun A => IsCyclic Φ A ∧ Φ A ≠ A)
  fix := Finset.univ.filter (fun A => Φ A = A)

/-- The recurrence layer recovers the multiplicity of exact solutions (gate
`S11` of v0.32). -/
theorem boundary_fix_card (Φ : Finset Bool → Finset Bool) :
    (boundaryOf Φ).fix.card = fixCount Φ := rfl

/-- Two transformers with the same partial layer and different recurrence
layers — the layers are logically independent. -/
theorem layers_independent :
    (boundaryOf liar).interval = (boundaryOf bifurcated).interval ∧
    (boundaryOf liar).fix ≠ (boundaryOf bifurcated).fix := by
  refine ⟨?_, by decide⟩
  show istep liar fullInterval = istep bifurcated fullInterval
  rw [liar_interval_fixed, bifurcated_interval_fixed]

end Boundary

end MetaLang
