import MetaLang.RefinementOrder

/-!
# Semantic reflection (v0.25)

The last "book" symbol `rho : S → S` used to be a source table. v0.25 asks
when a unary meaning operation is **forced** by continuation semantics. The
answer: when a semantic subspace `F` is given and

  `Ref_F(x) = Min { y ∈ F : x ≤ y }`

turns out to be a single point. Then `rho_F` is not merely a closure
operator but a **left adjoint** to the inclusion `F ↪ Q`. It is the
universal property, not the closure laws, that singles out the operation:
this is the no-go of §4.
-/

namespace MetaLang

universe u

section Reflection

variable {α : Type u} [PartialOrder α]

/-- `y` is the least point of `F` above `x`. -/
def IsReflectionAt (F : Set α) (x y : α) : Prop :=
  y ∈ F ∧ x ≤ y ∧ ∀ z ∈ F, x ≤ z → y ≤ z

/-- A subspace is reflective when above every point there is a least point
of `F`. -/
def Reflective (F : Set α) : Prop := ∀ x : α, ∃ y, IsReflectionAt F x y

theorem isReflectionAt_unique {F : Set α} {x y y' : α}
    (h : IsReflectionAt F x y) (h' : IsReflectionAt F x y') : y = y' :=
  le_antisymm (h.2.2 y' h'.1 h'.2.1) (h'.2.2 y h.1 h.2.1)

variable {F : Set α} (h : Reflective F)

/-- The reflector into `F`. -/
noncomputable def rho (x : α) : α := (h x).choose

theorem rho_spec (x : α) : IsReflectionAt F x (rho h x) := (h x).choose_spec

theorem rho_mem (x : α) : rho h x ∈ F := (rho_spec h x).1

/-- Inflationarity. -/
theorem le_rho (x : α) : x ≤ rho h x := (rho_spec h x).2.1

theorem rho_least {x z : α} (hz : z ∈ F) (hxz : x ≤ z) : rho h x ≤ z :=
  (rho_spec h x).2.2 z hz hxz

/-- **The universal adjunction.** For every point of `F`, passing to the
reflection does not change the relation: `rho_F` is left adjoint to the
inclusion. -/
theorem rho_le_iff {x f : α} (hf : f ∈ F) : rho h x ≤ f ↔ x ≤ f := by
  constructor
  · intro hle; exact le_trans (le_rho h x) hle
  · intro hle; exact rho_least h hf hle

/-- Monotonicity. -/
theorem rho_monotone : Monotone (rho h) := by
  intro x y hxy
  exact rho_least h (rho_mem h y) (le_trans hxy (le_rho h y))

/-- Idempotence. -/
theorem rho_idem (x : α) : rho h (rho h x) = rho h x :=
  le_antisymm (rho_least h (rho_mem h x) (le_refl _)) (le_rho h (rho h x))

/-- **The fixed space coincides with `F`.** -/
theorem rho_fix_iff (x : α) : rho h x = x ↔ x ∈ F := by
  constructor
  · intro hx; rw [← hx]; exact rho_mem h x
  · intro hx; exact le_antisymm (rho_least h hx (le_refl _)) (le_rho h x)

/-- `rho_F` as a Mathlib closure operator. -/
noncomputable def rhoClosure : ClosureOperator α where
  toFun := rho h
  monotone' := rho_monotone h
  le_closure' := le_rho h
  idempotent' := rho_idem h

@[simp] theorem rhoClosure_apply (x : α) : rhoClosure h x = rho h x := rfl

/-- The adjunction in `GaloisConnection` form between `α` and the subspace `F`. -/
theorem rho_galoisConnection :
    GaloisConnection (fun x : α => (⟨rho h x, rho_mem h x⟩ : F)) (fun f : F => (f : α)) := by
  intro x f
  exact rho_le_iff h f.2

end Reflection

/-! ### The joint reflector as a least upper bound -/

section Joint

variable {α : Type u} [PartialOrder α] {F G : Set α}

/-- **The joint reflector is the least upper bound** in the pointwise order
of closure operators: it dominates both reflectors and is least among such. -/
theorem joint_reflector_isLUB (hF : Reflective F) (hG : Reflective G)
    (hFG : Reflective (F ∩ G)) :
    (∀ x, rho hF x ≤ rho hFG x) ∧ (∀ x, rho hG x ≤ rho hFG x) ∧
      ∀ e : ClosureOperator α, (∀ x, rho hF x ≤ e x) → (∀ x, rho hG x ≤ e x) →
        ∀ x, rho hFG x ≤ e x := by
  refine ⟨fun x => rho_least hF (rho_mem hFG x).1 (le_rho hFG x),
          fun x => rho_least hG (rho_mem hFG x).2 (le_rho hFG x), ?_⟩
  intro e hce hde x
  have hFe : e x ∈ F := by
    rw [← rho_fix_iff hF]
    exact le_antisymm (le_trans (hce (e x)) (le_of_eq (e.idempotent x))) (le_rho hF (e x))
  have hGe : e x ∈ G := by
    rw [← rho_fix_iff hG]
    exact le_antisymm (le_trans (hde (e x)) (le_of_eq (e.idempotent x))) (le_rho hG (e x))
  exact rho_least hFG ⟨hFe, hGe⟩ (e.le_closure' x)

end Joint

/-! ### No-go: the closure laws are not enough

On every nontrivial bounded order, the identity operator and the
"everything to the top" operator are both inflationary, monotone and
idempotent, yet distinct. So the order plus the closure axioms do **not**
determine a unary meaning operation; the target subspace is necessary. -/

section NoGo

variable {α : Type u} [PartialOrder α] [OrderTop α]

/-- The "everything to the top" operator. -/
def topClosure : ClosureOperator α where
  toFun := fun _ => ⊤
  monotone' := fun _ _ _ => le_refl _
  le_closure' := fun _ => le_top
  idempotent' := fun _ => rfl

/-- **Closure is not enough.** There are two distinct closure operators on
one and the same order. -/
theorem closure_laws_do_not_determine_reflection {x : α} (hx : x ≠ ⊤) :
    ∃ c d : ClosureOperator α, c ≠ d := by
  refine ⟨ClosureOperator.id α, topClosure, ?_⟩
  intro hEq
  have : (ClosureOperator.id α) x = (topClosure : ClosureOperator α) x := by rw [hEq]
  exact hx this

end NoGo

/-! ### Countermodel: a non-reflective subspace

In the diamond, the subspace of two incomparable atoms is not reflective:
above `bot` it has two minimal elements and no least one. -/

instance (F : Set M3) [DecidablePred (· ∈ F)] (x y : M3) :
    Decidable (IsReflectionAt F x y) := by
  unfold IsReflectionAt
  infer_instance

/-- **A non-reflective subspace.** `{a, b}` has no least element above
`bot`: reflection here is multivalued. -/
theorem m3_pair_not_reflective : ¬ Reflective ({M3.a, M3.b} : Set M3) := by
  intro hrefl
  obtain ⟨y, hy⟩ := hrefl M3.bot
  have hmem : y = M3.a ∨ y = M3.b := hy.1
  have hle_a : y ≤ M3.a := hy.2.2 M3.a (by simp) (by decide)
  have hle_b : y ≤ M3.b := hy.2.2 M3.b (by simp) (by decide)
  rcases hmem with rfl | rfl
  · exact absurd hle_b (by decide)
  · exact absurd hle_a (by decide)

end MetaLang
