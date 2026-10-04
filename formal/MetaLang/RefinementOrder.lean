import Mathlib

/-!
# The refinement order and universal synthesis (v0.24)

Meaning operations are not supplied by a source table; they are **derived**
from continuation structure by universal properties.

The refinement order:

  `x ≤_A y  ⟺  Paths y ⊆ Paths x`

that is, `y` is at least as constrained as `x`: every future admissible from
`y` was already admissible from `x`.

Synthesis is the least common refinement, i.e. the least upper bound. The
main content of v0.24 §3.1: idempotence, commutativity and associativity of
synthesis are **not postulated** but follow from the symmetric universal
property. And the main limitation (§4): the continuation order by itself
does **not** determine an arbitrary binary operation.
-/

namespace MetaLang

universe u

/-! ### The order from the continuation language -/

/-- A continuation system with **partial** admissibility: an action may be
inapplicable in a given state. -/
structure ContSystem where
  /-- Semantic points. -/
  St : Type u
  /-- Continuations. -/
  Act : Type u
  /-- The partial action. -/
  step : Act → St → Option St

namespace ContSystem

/-- Running a word of continuations; `none` means the word is inadmissible. -/
def run (S : ContSystem) : List S.Act → S.St → Option S.St
  | [], s => some s
  | a :: w, s => (S.step a s).bind (run S w)

variable (S : ContSystem)

/-- The admissible continuation language of a point. -/
def Paths (x : S.St) : Set (List S.Act) := {w | (S.run w x).isSome}

/-- The refinement order: `y` is more constrained than `x`. -/
def refines (x y : S.St) : Prop := S.Paths y ⊆ S.Paths x

variable {S}

theorem refines_refl (x : S.St) : S.refines x x := subset_rfl

theorem refines_trans {x y z : S.St} (h₁ : S.refines x y) (h₂ : S.refines y z) :
    S.refines x z := fun w hw => h₁ (h₂ hw)

/-- The substantive reading: refinement means that no admissible future has
appeared anew. -/
theorem refines_iff (x y : S.St) :
    S.refines x y ↔ ∀ w : List S.Act, (S.run w y).isSome → (S.run w x).isSome :=
  Iff.rfl

/-- **Antisymmetry up to the continuation language.** Mutual refinement
means the languages coincide; hence on the quotient by language equality
`refines` becomes a partial order. -/
theorem refines_antisymm {x y : S.St} (h₁ : S.refines x y) (h₂ : S.refines y x) :
    S.Paths x = S.Paths y :=
  Set.Subset.antisymm h₂ h₁

/-- Identification of points with the same continuation language. -/
def pathSetoid (S : ContSystem) : Setoid S.St where
  r x y := S.Paths x = S.Paths y
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The empty word is always admissible, so continuation languages are nonempty. -/
theorem nil_mem_paths (x : S.St) : [] ∈ S.Paths x := by
  simp [Paths, run]

end ContSystem

/-! ### Universal synthesis

What follows is pure order theory. Synthesis is defined as a least upper
bound, and all of its laws are derived from that definition. -/

section Synthesis

variable {α : Type u} [PartialOrder α]

/-- A synthesis `z` of the points `x` and `y` — the least common refinement. -/
def IsSynthesis (x y z : α) : Prop := IsLUB {x, y} z

/-- Synthesis is unique when it exists. -/
theorem isSynthesis_unique {x y z z' : α}
    (h : IsSynthesis x y z) (h' : IsSynthesis x y z') : z = z' :=
  IsLUB.unique h h'

/-- **Idempotence** — from the universal property. -/
theorem isSynthesis_idem (x : α) : IsSynthesis x x x := by
  constructor
  · rintro b (rfl | rfl) <;> exact le_refl _
  · intro b hb
    exact hb (by simp)

/-- **Commutativity** — from the symmetry of the pair. -/
theorem isSynthesis_comm {x y z : α} (h : IsSynthesis x y z) : IsSynthesis y x z := by
  unfold IsSynthesis at h ⊢
  rwa [Set.pair_comm]

/-- The synthesis of a pair is exactly the least upper bound of a two-element
set; hence the bridge to a triple synthesis. -/
theorem isLUB_triple_of_left {x y z u v : α}
    (hu : IsSynthesis x y u) (hv : IsSynthesis u z v) : IsLUB {x, y, z} v := by
  constructor
  · rintro b (rfl | rfl | rfl)
    · exact le_trans (hu.1 (by simp)) (hv.1 (by simp))
    · exact le_trans (hu.1 (by simp)) (hv.1 (by simp))
    · exact hv.1 (by simp)
  · intro b hb
    refine hv.2 ?_
    rintro c (rfl | rfl)
    · exact hu.2 (fun d hd => hb (by rcases hd with rfl | rfl <;> simp))
    · exact hb (by simp)

theorem isLUB_triple_of_right {x y z w v : α}
    (hw : IsSynthesis y z w) (hv : IsSynthesis x w v) : IsLUB {x, y, z} v := by
  constructor
  · rintro b (rfl | rfl | rfl)
    · exact hv.1 (by simp)
    · exact le_trans (hw.1 (by simp)) (hv.1 (by simp))
    · exact le_trans (hw.1 (by simp)) (hv.1 (by simp))
  · intro b hb
    refine hv.2 ?_
    rintro c (rfl | rfl)
    · exact hb (by simp)
    · exact hw.2 (fun d hd => hb (by rcases hd with rfl | rfl <;> simp))

/-- **Associativity** — from the universal property, not from an axiom. Both
bracketings are the least upper bound of the same triple. -/
theorem isSynthesis_assoc {x y z u v w v' : α}
    (hu : IsSynthesis x y u) (hv : IsSynthesis u z v)
    (hw : IsSynthesis y z w) (hv' : IsSynthesis x w v') : v = v' :=
  IsLUB.unique (isLUB_triple_of_left hu hv) (isLUB_triple_of_right hw hv')

end Synthesis

/-! ### No-go: the order does not determine an arbitrary operation

For every nontrivial order, both projections are total, monotone in each
argument, and distinct. So the continuation order alone is not enough to
single out a binary operation: a universal property is needed. -/

theorem order_does_not_determine_binop {α : Type u} [PartialOrder α]
    {x y : α} (hxy : x ≠ y) :
    ∃ f g : α → α → α,
      (∀ a : α, Monotone (f a)) ∧ (∀ b : α, Monotone (fun a => f a b)) ∧
      (∀ a : α, Monotone (g a)) ∧ (∀ b : α, Monotone (fun a => g a b)) ∧
      f ≠ g := by
  refine ⟨fun a _ => a, fun _ b => b, fun a => monotone_const, fun b => monotone_id,
    fun a => monotone_id, fun b => monotone_const, ?_⟩
  intro hEq
  exact hxy (congrFun (congrFun hEq x) y)

/-! ### Contrast

`Contrast x y` — the minimal `z` whose addition to `y` reaches `x`. In
general this is an **antichain**, not a point. -/

/-- The canonical contrast: the minimal augmentations. -/
def Contrast {α : Type u} [Lattice α] (x y : α) : Set α :=
  {z | x ≤ y ⊔ z ∧ ∀ w, x ≤ y ⊔ w → w ≤ z → w = z}

/-! ### The diamond `M3` — witness of a multivalued contrast

The non-distributive lattice from the corpus (the `M3 x chain` family in
v0.24–v0.27). Three incomparable atoms give a pair whose contrast is an
antichain of two points. -/

/-- The diamond: `bot`, three pairwise incomparable atoms, `top`. -/
inductive M3 where
  /-- The bottom element. -/
  | bot
  /-- The first atom. -/
  | a
  /-- The second atom. -/
  | b
  /-- The third atom. -/
  | c
  /-- The top element. -/
  | top
  deriving DecidableEq, Fintype, Repr

namespace M3

/-- The order of the diamond. -/
def leB : M3 → M3 → Bool
  | .bot, _ => true
  | _, .top => true
  | x, y => x == y

instance : LE M3 := ⟨fun x y => leB x y = true⟩

instance decLE : DecidableRel ((· ≤ ·) : M3 → M3 → Prop) :=
  fun x y => inferInstanceAs (Decidable (leB x y = true))

/-- The least upper bound. -/
def supM : M3 → M3 → M3
  | .bot, y => y
  | x, .bot => x
  | .top, _ => .top
  | _, .top => .top
  | x, y => if x = y then x else .top

/-- The greatest lower bound. -/
def infM : M3 → M3 → M3
  | .top, y => y
  | x, .top => x
  | .bot, _ => .bot
  | _, .bot => .bot
  | x, y => if x = y then x else .bot

instance : Lattice M3 where
  le := (· ≤ ·)
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  sup := supM
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf := infM
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : OrderTop M3 where
  top := M3.top
  le_top := by decide

instance : OrderBot M3 where
  bot := M3.bot
  bot_le := by decide

/-- The atoms are pairwise incomparable — the lattice really is a diamond. -/
theorem atoms_incomparable : ¬ (M3.a ≤ M3.b) ∧ ¬ (M3.b ≤ M3.a) := by decide

end M3

instance (x y z : M3) : Decidable (z ∈ Contrast x y) := by
  unfold Contrast
  rw [Set.mem_setOf_eq]
  infer_instance

/-- **Contrast is multivalued.** In the diamond, `Contrast top a` contains
two distinct minimal augmentations: `b` and `c`. The continuation order does
not determine a point-valued contrast operation. -/
theorem m3_contrast_multivalued :
    M3.b ∈ Contrast M3.top M3.a ∧ M3.c ∈ Contrast M3.top M3.a ∧ M3.b ≠ M3.c := by
  refine ⟨by decide, by decide, by decide⟩

/-- The general form: there is a lattice in which the contrast is an
antichain of size at least two. -/
theorem contrast_can_be_multivalued :
    ∃ (β : Type) (_ : Lattice β) (x y u v : β),
      u ∈ Contrast x y ∧ v ∈ Contrast x y ∧ u ≠ v :=
  ⟨M3, inferInstance, M3.top, M3.a, M3.b, M3.c,
   m3_contrast_multivalued.1, m3_contrast_multivalued.2.1, m3_contrast_multivalued.2.2⟩

/-! ### The refinement interface: the order is recovered from behaviour

Gates `S1`, `S2` of v0.24. In the experiment the order is not read off a
state label: for every point `z` there is an idempotent continuation `r_z`,
admissible at `x` exactly when `x ≤ z`. Below are that construction and the
theorem that the continuation language recovers it completely. -/

namespace RefinementInterface

variable (P : Type u) [PartialOrder P] [DecidableRel ((· ≤ ·) : P → P → Prop)]

/-- A source-free continuation system: the continuation `z` is admissible at
`x` exactly when `x ≤ z`, and it sends `x` to `z`. -/
abbrev sys : ContSystem where
  St := P
  Act := P
  step := fun z x => if x ≤ z then some z else none

variable {P}

@[simp] theorem run_cons_isSome (z : P) (w : List P) (s : P) :
    ((sys P).run (z :: w) s).isSome ↔ s ≤ z ∧ ((sys P).run w z).isSome := by
  by_cases h : s ≤ z
  · simp [ContSystem.run, sys, h]
  · simp [ContSystem.run, sys, h]

theorem run_singleton (x : P) : (sys P).run [x] x = some x := by
  simp [ContSystem.run]

/-- **The refinement primitive is idempotent** (gates `S5` of v0.18, `S2` of
v0.19, `S1` of v0.20). Applying the same continuation twice changes nothing:
the first application already moved the point to `z`, and `z ≤ z`. -/
theorem run_idempotent (z x : P) (h : x ≤ z) :
    (sys P).run [z, z] x = (sys P).run [z] x := by
  simp [ContSystem.run, h]

theorem mem_paths_singleton (x : P) : [x] ∈ (sys P).Paths x := by
  show ((sys P).run [x] x).isSome = true
  rw [run_singleton]
  rfl

/-- **The order is recovered from the continuation language (gates `S1`,
`S2`).** No state label takes part: inclusion of continuation languages
reproduces the refinement order exactly. -/
theorem refines_iff_le (x y : P) : (sys P).refines x y ↔ x ≤ y := by
  constructor
  · intro h
    have hmem := h (mem_paths_singleton y)
    by_contra hxy
    have hnone : (sys P).run [y] x = none := by
      simp [ContSystem.run, hxy]
    have : ((sys P).run [y] x).isSome = true := hmem
    rw [hnone] at this
    exact absurd this (by simp)
  · intro hxy w hw
    cases w with
    | nil => exact hw
    | cons z w =>
        have hz := (run_cons_isSome z w y).mp hw
        exact (run_cons_isSome z w x).mpr ⟨le_trans hxy hz.1, hz.2⟩

end RefinementInterface

/-! ### The Boolean case: contrast is a singleton (gate `S13` of v0.24) -/

/-- **In a Boolean algebra contrast is point-valued.** The antichain of
minimal augmentations degenerates to the single point `x \ y`; this is the
special case in which the old type `Q × Q → Q` is legitimate. -/
theorem boolean_contrast_singleton {α : Type u} [BooleanAlgebra α] (x y : α) :
    Contrast x y = {x \ y} := by
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨le_sup_sdiff, ?_⟩, ?_⟩
  · intro w hw hle
    exact le_antisymm hle (sdiff_le_iff.mpr hw)
  · rintro z ⟨hz, hmin⟩
    exact (hmin (x \ y) le_sup_sdiff (sdiff_le_iff.mpr hz)).symm

/-! ### The non-lattice boundary: synthesis may not exist (gates `S9`, `S10` of v0.24) -/

/-- The "bowtie": `a, b` are incomparable and both lie below the incomparable `c, d`. -/
inductive Bow where
  /-- The first lower element. -/
  | a
  /-- The second lower element. -/
  | b
  /-- The first upper element. -/
  | c
  /-- The second upper element. -/
  | d
  deriving DecidableEq, Fintype, Repr

namespace Bow

/-- The order of the bowtie. -/
def leB : Bow → Bow → Bool
  | .a, .a => true
  | .a, .c => true
  | .a, .d => true
  | .b, .b => true
  | .b, .c => true
  | .b, .d => true
  | .c, .c => true
  | .d, .d => true
  | _, _ => false

instance : LE Bow := ⟨fun x y => leB x y = true⟩

instance decLE : DecidableRel ((· ≤ ·) : Bow → Bow → Prop) :=
  fun x y => decEq (leB x y) true

instance : PartialOrder Bow where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

end Bow

/-- **The non-lattice boundary.** The pair `a, b` has two incomparable
minimal upper bounds, so no least common refinement exists: ASC does **not**
force a semilattice, and synthesis is a partial operation. -/
theorem bow_no_synthesis : ¬ ∃ z : Bow, IsSynthesis Bow.a Bow.b z := by
  rintro ⟨z, hub, hle⟩
  have ha : Bow.a ≤ z := hub (by simp)
  have hb : Bow.b ≤ z := hub (by simp)
  have hc : z ≤ Bow.c := hle (by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;> decide)
  have hd : z ≤ Bow.d := hle (by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl <;> decide)
  revert ha hb hc hd
  cases z <;> decide

/-- The general form: there is a partial order on which synthesis is not total. -/
theorem synthesis_is_partial :
    ∃ (β : Type) (_ : PartialOrder β) (x y : β), ¬ ∃ z, IsSynthesis x y z :=
  ⟨Bow, inferInstance, Bow.a, Bow.b, bow_no_synthesis⟩

/-! ### Synthesis is determined by the continuation language
(v0.24 `S3`–`S5`, `S11`, `S12`, `S17`)

The corpus requires not only that universal synthesis exist, but that it be
**computed without a source operation**: the only input is the admissible
continuation language. Three statements record this: synthesis is
reformulated through `refines`; it is invariant under every order
isomorphism (so two independent observers get the same answer); and it is
total on lattices. -/

namespace RefinementInterface

variable {P : Type u} [PartialOrder P] [DecidableRel ((· ≤ ·) : P → P → Prop)]

/-- **Synthesis is computed without a source operation (gate `S3` of
v0.24).** The right-hand side speaks only of inclusion of continuation
languages: no operation table enters it. -/
theorem isSynthesis_iff_paths (x y z : P) :
    IsSynthesis x y z ↔
      ((sys P).refines x z ∧ (sys P).refines y z ∧
        ∀ w : P, (sys P).refines x w → (sys P).refines y w → (sys P).refines z w) := by
  simp only [refines_iff_le]
  constructor
  · rintro ⟨hub, hle⟩
    refine ⟨hub (by simp), hub (by simp), fun w hx hy => hle ?_⟩
    rintro b (rfl | rfl)
    · exact hx
    · exact hy
  · rintro ⟨hx, hy, hmin⟩
    constructor
    · rintro b (rfl | rfl)
      · exact hx
      · exact hy
    · intro w hw
      exact hmin w (hw (by simp)) (hw (by simp))

end RefinementInterface

/-- **Independent observers obtain the same synthesis (gate `S4` of
v0.24).** Synthesis is invariant under every order isomorphism, so relabeling
surface symbols does not change it. -/
theorem isSynthesis_orderIso {α β : Type u} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) {x y z : α} (h : IsSynthesis x y z) :
    IsSynthesis (e x) (e y) (e z) := by
  obtain ⟨hub, hle⟩ := h
  constructor
  · rintro b (rfl | rfl) <;> rw [e.le_iff_le]
    · exact hub (by simp)
    · exact hub (by simp)
  · intro u hu
    obtain ⟨w, rfl⟩ := e.surjective u
    rw [e.le_iff_le]
    refine hle ?_
    rintro b (rfl | rfl)
    · exact (e.le_iff_le).mp (hu (by simp))
    · exact (e.le_iff_le).mp (hu (by simp))

/-- **Independent observers obtain the same contrast antichain (gate `S12`
of v0.24).** -/
theorem contrast_orderIso {α β : Type u} [Lattice α] [Lattice β]
    (e : α ≃o β) (x y : α) : Contrast (e x) (e y) = e '' Contrast x y := by
  have hsup : ∀ a b : α, e (a ⊔ b) = e a ⊔ e b := fun a b => e.map_sup a b
  ext u
  constructor
  · rintro ⟨hmem, hmin⟩
    obtain ⟨z, rfl⟩ := e.surjective u
    refine ⟨z, ⟨?_, ?_⟩, rfl⟩
    · rw [← e.le_iff_le, hsup]; exact hmem
    · intro w hw hwz
      have h1 : e x ≤ e y ⊔ e w := by rw [← hsup, e.le_iff_le]; exact hw
      have h2 : e w ≤ e z := (e.le_iff_le).mpr hwz
      exact e.injective (hmin (e w) h1 h2)
  · rintro ⟨z, ⟨hmem, hmin⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← hsup, e.le_iff_le]; exact hmem
    · intro w hw hwz
      obtain ⟨v, rfl⟩ := e.surjective w
      have h1 : x ≤ y ⊔ v := by rw [← e.le_iff_le, hsup]; exact hw
      have h2 : v ≤ z := (e.le_iff_le).mp hwz
      rw [hmin v h1 h2]

/-- **On a lattice synthesis is total (gate `S5` of v0.24).** -/
theorem lattice_total_synthesis {α : Type u} [Lattice α] (x y : α) :
    IsSynthesis x y (x ⊔ y) := isLUB_pair

/-- **The contrast antichain is nonempty on a finite lattice (gate `S11` of
v0.24).** The set of augmentations contains `x` itself, and a finite nonempty
set has a minimal element — so contrast is always defined, even if not
point-valued. -/
theorem contrast_nonempty {α : Type u} [Lattice α] [Finite α] (x y : α) :
    (Contrast x y).Nonempty := by
  obtain ⟨z, hz, hmin⟩ :=
    Set.Finite.exists_minimal (s := {z : α | x ≤ y ⊔ z})
      (Set.toFinite _) ⟨x, le_sup_right⟩
  exact ⟨z, hz, fun w hw hwz => le_antisymm hwz (hmin hw hwz)⟩

/-- **The order does not single out a binary operation (gate `S17` of
v0.24).** A strengthening of `order_does_not_determine_binop` to the corpus
form: both projections are monotone in the **product** order and total — and
still they disagree on a concrete pair. -/
theorem binop_not_identified_by_order {α : Type u} [PartialOrder α]
    {x y : α} (hxy : x ≠ y) :
    ∃ f g : α → α → α,
      (∀ a b a' b' : α, a ≤ a' → b ≤ b' → f a b ≤ f a' b') ∧
      (∀ a b a' b' : α, a ≤ a' → b ≤ b' → g a b ≤ g a' b') ∧
      f x y ≠ g x y :=
  ⟨fun a _ => a, fun _ b => b, fun _ _ _ _ ha _ => ha, fun _ _ _ _ _ hb => hb, hxy⟩

end MetaLang
