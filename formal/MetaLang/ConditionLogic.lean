import MetaLang.JointReflection

/-!
# The abstract logic of conditions (v0.27, the order-theoretic part)

`ConstraintLogic.lean` works with the concrete carrier `B3` and an
enumeration of 61 Moore families. Here is what v0.27 proves by **order**
rather than by enumeration, and which is therefore stated for an arbitrary
lattice.

* **Entailment = absorption = the reverse order of reflectors** (`S9`). A
  condition `c` entails `d` exactly when `d ≤ c` pointwise as operators: the
  logic of conditions is the order of reflectors, turned upside down.
* **The lattice laws** (`S7`): associativity, commutativity and absorption
  with the hull disjunction.
* **Implication and negation are multi-valued in general** (`S15`, `S16`):
  in the diamond the residual `a → ⊥` is a two-point antichain.
* **The implication antichain is a complete generalized residual** (`S17`):
  on a finite lattice every `z` with `x ⊓ z ≤ y` lies below one of its
  elements.

The enumerative half of v0.27 (`S10`, `S13`, `S14`, `S22`, `S24`, `S25`) and
all of v0.28 belong to milestone M13d — see `PRD_BACKLOG.md`.
-/

namespace MetaLang

universe u

/-! ## Entailment of conditions -/

section Entailment

variable {α : Type u} [PartialOrder α]

/-- A condition `c` **entails** `d` when every point closed under `c` is
also closed under `d`: the fixed space of `c` is contained in the fixed space
of `d`. -/
def Entails (c d : ClosureOperator α) : Prop := ∀ x : α, c x = x → d x = x

/-- **Entailment is the reverse order of reflectors (gate `S9` of v0.27).**
The logic of conditions is the order of closure operators turned upside down:
a stronger condition is a larger reflector. -/
theorem entails_iff_reverse_order (c d : ClosureOperator α) :
    Entails c d ↔ ∀ x : α, d x ≤ c x := by
  constructor
  · intro h x
    have hcx : c (c x) = c x := c.idempotent x
    have hfix : d (c x) = c x := h (c x) hcx
    calc d x ≤ d (c x) := d.monotone (c.le_closure x)
      _ = c x := hfix
  · intro h x hx
    refine le_antisymm ?_ (d.le_closure x)
    calc d x ≤ c x := h x
      _ = x := hx

/-- Entailment is reflexive and transitive. -/
theorem entails_refl (c : ClosureOperator α) : Entails c c := fun _ h => h

theorem entails_trans {c d e : ClosureOperator α}
    (h₁ : Entails c d) (h₂ : Entails d e) : Entails c e :=
  fun x hx => h₂ x (h₁ x hx)

end Entailment

/-! ## The lattice laws for conditions -/

section LatticeLaws

variable {α : Type u} [Lattice α]

/-- **Absorption with the hull disjunction (gate `S7` of v0.27).** The
disjunction of conditions is the hull of the join; absorption holds precisely
because the hull is inflationary. -/
theorem absorption_of_closure (h : ClosureOperator α) (x y : α) :
    x ⊓ h (x ⊔ y) = x :=
  inf_eq_left.mpr (le_trans le_sup_left (h.le_closure _))

/-- Conjunction of conditions is associative and commutative — these are
lattice laws of the carrier, not separate axioms of the logic. -/
theorem conj_assoc (x y z : α) : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := inf_assoc x y z

theorem conj_comm (x y : α) : x ⊓ y = y ⊓ x := inf_comm x y

/-- The hull disjunction is commutative. -/
theorem disj_comm (h : ClosureOperator α) (x y : α) : h (x ⊔ y) = h (y ⊔ x) := by
  rw [sup_comm]

end LatticeLaws

/-! ## Implication as an antichain -/

section Residual

variable {α : Type u} [Lattice α]

/-- The implication antichain: the maximal `z` for which `x ⊓ z` still does
not exceed `y`. -/
def ImpAntichain (x y : α) : Set α :=
  {z | x ⊓ z ≤ y ∧ ∀ w, x ⊓ w ≤ y → z ≤ w → w = z}

/-- **The implication antichain is a complete generalized residual (gate
`S17` of v0.27).** On a finite lattice every candidate lies below one of its
elements: the antichain loses no solutions. -/
theorem impAntichain_complete [Finite α] (x y z : α) (hz : x ⊓ z ≤ y) :
    ∃ m ∈ ImpAntichain x y, z ≤ m := by
  obtain ⟨m, hm, hmax⟩ :=
    Set.Finite.exists_maximal (s := {w : α | x ⊓ w ≤ y ∧ z ≤ w})
      (Set.toFinite _) ⟨z, hz, le_refl z⟩
  refine ⟨m, ⟨hm.1, ?_⟩, hm.2⟩
  intro w hw hmw
  exact le_antisymm (hmax ⟨hw, le_trans hm.2 hmw⟩ hmw) hmw

/-- When the implication antichain is a singleton, exact residuation holds. -/
theorem residuation_of_singleton [Finite α] {x y m : α}
    (hm : ImpAntichain x y = {m}) (z : α) : x ⊓ z ≤ y ↔ z ≤ m := by
  constructor
  · intro hz
    obtain ⟨m', hm', hzm'⟩ := impAntichain_complete x y z hz
    rw [hm] at hm'
    rwa [← hm']
  · intro hz
    have hmem : m ∈ ImpAntichain x y := by rw [hm]; rfl
    exact le_trans (inf_le_inf_left x hz) hmem.1

end Residual

/-! ## Multi-valuedness of implication and negation in the diamond -/

namespace DiamondLogic

/-- **Implication is multi-valued in general (gate `S15` of v0.27).** In the
diamond, `a → ⊥` contains two incomparable maximal elements. -/
theorem impAntichain_multivalued :
    M3.b ∈ ImpAntichain M3.a M3.bot ∧ M3.c ∈ ImpAntichain M3.a M3.bot ∧
      M3.b ≠ M3.c := by
  refine ⟨⟨by decide, ?_⟩, ⟨by decide, ?_⟩, by decide⟩
  · intro w hw hbw
    revert hw hbw
    revert w
    decide
  · intro w hw hcw
    revert hw hcw
    revert w
    decide

/-- **Negation is multi-valued in general (gate `S16` of v0.27).** Negation
is implication into `⊥`, and it inherits the same antichain. -/
theorem negation_multivalued :
    ∃ u v : M3, u ∈ ImpAntichain M3.a M3.bot ∧ v ∈ ImpAntichain M3.a M3.bot ∧ u ≠ v :=
  ⟨M3.b, M3.c, impAntichain_multivalued.1, impAntichain_multivalued.2.1,
    impAntichain_multivalued.2.2⟩

end DiamondLogic

end MetaLang
