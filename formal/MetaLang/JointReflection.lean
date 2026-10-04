import MetaLang.ReflectionTheory
import MetaLang.ReflectorAlgebra

/-!
# The algebra of reflectors: independence, feedback, saturation (v0.26)

`ReflectorAlgebra.lean` supplies the core: `Fix (c ∘ d) = Fix c ∩ Fix d`,
non-idempotence of the raw composite, saturation on a finite order. What the
corpus builds around that core is filled in here.

**Independence.** If two constraints act on disjoint coordinates, their
reflectors commute — and then the composite is itself a reflection into the
intersection (`S6`, `S7`). The converse fails: commuting does not require
independence (`S8`).

**Feedback.** The main missing witness: a pair of reflectors for which **no**
single-pass order gives a joint reflector (`S14`). The `Fin 4` pair of
`ReflectorAlgebra.lean` is not enough for this — one of its orders is "good".
The witness is built on the chain `Fin 5`; it also shows that non-commuting
cases require iteration (`S18`), and that saturating either order arrives at
the same point (`S16`, `S17`).

**The infinite case.** The reflections of the Boolean witness commute, their
composite is a reflector into the intersection of the subspaces, and it is
ASC-continuous (`S21`, `S22`).
-/

namespace MetaLang

universe u

/-! ## The principal reflector -/

/-- **A primitive is a reflector (gate `S1` of v0.26).** Adjoining `κ` is a
closure operator: inflationary, monotone, idempotent. -/
def principalClosure {α : Type u} [Lattice α] (κ : α) : ClosureOperator α where
  toFun := fun x => κ ⊔ x
  monotone' := fun _ _ h => sup_le_sup_left h κ
  le_closure' := fun _ => le_sup_right
  idempotent' := fun x => by
    simp [sup_assoc]

@[simp] theorem principalClosure_apply {α : Type u} [Lattice α] (κ x : α) :
    principalClosure κ x = κ ⊔ x := rfl

/-! ## Independence implies commuting -/

section Independence

variable {β γ : Type u} [PartialOrder β] [PartialOrder γ]

/-- The reflector acting on the first coordinate only. -/
def leftOp (c : ClosureOperator β) : ClosureOperator (β × γ) where
  toFun := fun p => (c p.1, p.2)
  monotone' := fun _ _ h => ⟨c.monotone h.1, h.2⟩
  le_closure' := fun p => ⟨c.le_closure p.1, le_refl p.2⟩
  idempotent' := fun p => by
    simp [c.idempotent]

/-- The reflector acting on the second coordinate only. -/
def rightOp (d : ClosureOperator γ) : ClosureOperator (β × γ) where
  toFun := fun p => (p.1, d p.2)
  monotone' := fun _ _ h => ⟨h.1, d.monotone h.2⟩
  le_closure' := fun p => ⟨le_refl p.1, d.le_closure p.2⟩
  idempotent' := fun p => by
    simp [d.idempotent]

/-- **Independence in the source implies commuting (gate `S6` of v0.26).**
Constraints on disjoint coordinates are interchangeable. -/
theorem independent_commute (c : ClosureOperator β) (d : ClosureOperator γ) :
    ∀ p : β × γ, leftOp c (rightOp d p) = rightOp d (leftOp c p) := by
  intro p
  rfl

/-- **Commuting independent reflectors yield a joint reflection (gate `S7`
of v0.26).** -/
theorem independent_comp_idempotent (c : ClosureOperator β) (d : ClosureOperator γ) :
    ∀ p : β × γ, leftOp c (rightOp d (leftOp c (rightOp d p)))
      = leftOp c (rightOp d p) := by
  intro p
  exact comp_idempotent_of_commute (leftOp c) (rightOp d) (independent_commute c d) p

end Independence

/-- **Independence is not necessary for commuting (gate `S8` of v0.26).** An
operator commutes with itself, while its constraints are plainly not
independent: the fixed spaces coincide and are nontrivial. -/
theorem commute_without_independence :
    ∃ c d : ClosureOperator (Fin 4),
      (∀ x, c (d x) = d (c x)) ∧
      (∀ x, c x = x ↔ d x = x) ∧
      (∃ x, c x ≠ x) :=
  ⟨cOp, cOp, fun _ => rfl, fun _ => Iff.rfl, ⟨0, by decide⟩⟩

/-! ## A feedback pair: both single-pass orders are bad -/

namespace Feedback

/-- The first reflector of the chain `Fin 5`: `1`, `3`, `4` are fixed. -/
def fC : Fin 5 → Fin 5
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 3
  | 4 => 4

/-- The second reflector: `2` and `4` are fixed. -/
def fD : Fin 5 → Fin 5
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 4
  | 4 => 4

/-- The first one as a closure operator. -/
def C : ClosureOperator (Fin 5) where
  toFun := fC
  monotone' := by decide
  le_closure' := by decide
  idempotent' := by decide

/-- The second one as a closure operator. -/
def D : ClosureOperator (Fin 5) where
  toFun := fD
  monotone' := by decide
  le_closure' := by decide
  idempotent' := by decide

/-- The joint fixed space is a single point. -/
theorem joint_fixed (x : Fin 5) : (C x = x ∧ D x = x) ↔ x = 4 := by
  revert x
  decide

/-- **No single-pass order gives a joint reflector (gate `S14` of v0.26).**
At the point `0` both composites miss the unique common fixed point. -/
theorem neither_order_is_joint :
    C (D 0) ≠ 4 ∧ D (C 0) ≠ 4 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The two composites disagree — the order is observable. -/
theorem orders_differ : C (D 0) ≠ D (C 0) := by decide

/-- **Non-commuting cases need iteration (gate `S18` of v0.26).** One pass
is not enough, two suffice. -/
theorem iteration_needed :
    iter (fun x => C (D x)) 1 0 ≠ 4 ∧ iter (fun x => C (D x)) 2 0 = 4 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **Saturation recovers the joint reflector in both orders (gates `S16`,
`S17` of v0.26).** -/
theorem saturation_both_orders :
    iter (fun x => C (D x)) 2 0 = 4 ∧ iter (fun x => D (C x)) 2 0 = 4 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Saturation lands exactly on the joint fixed point. -/
theorem saturation_is_joint :
    C (iter (fun x => C (D x)) 2 0) = iter (fun x => C (D x)) 2 0 ∧
    D (iter (fun x => C (D x)) 2 0) = iter (fun x => C (D x)) 2 0 := by
  refine ⟨?_, ?_⟩ <;> decide

end Feedback

/-! ## The infinite case: composing reflections (v0.26 `S21`, `S22`) -/

namespace InfiniteJoint

open Witnesses
open Witnesses.InfiniteReflection (Target)

variable (A B : ℕ → Bool)

/-- The composite of two Boolean reflections is again a reflection, with the
union of the masks. -/
theorem refl_comp (x : ℕ → Bool) :
    InfiniteReflection.refl A (InfiniteReflection.refl B x)
      = InfiniteReflection.refl (fun i => A i || B i) x := by
  funext i
  cases hA : A i <;> cases hB : B i <;> cases hx : x i <;>
    simp [InfiniteReflection.refl, hA, hB, hx]

/-- Boolean reflections commute. -/
theorem refl_comm (x : ℕ → Bool) :
    InfiniteReflection.refl A (InfiniteReflection.refl B x)
      = InfiniteReflection.refl B (InfiniteReflection.refl A x) := by
  rw [refl_comp, refl_comp]
  funext i
  cases hA : A i <;> cases hB : B i <;> simp [InfiniteReflection.refl, hA, hB]

/-- **Saturating the chain recovers the joint constraint (gate `S21` of
v0.26).** The intersection of the target subspaces is exactly the subspace of
the union mask. -/
theorem joint_target :
    Target (fun i => A i || B i) = Target A ∩ Target B := by
  ext x
  constructor
  · intro h
    exact ⟨fun i hi => h i (by simp [hi]), fun i hi => h i (by simp [hi])⟩
  · rintro ⟨hA, hB⟩ i hi
    rcases Bool.or_eq_true_iff.mp hi with h | h
    · exact hA i h
    · exact hB i h

/-- **A composite of reflections is ASC-continuous (gate `S22` of v0.26).** -/
theorem comp_filtrationCompat :
    (shiftMachine Bool).FiltrationCompat₁
      (fun x => InfiniteReflection.refl A (InfiniteReflection.refl B x)) := by
  have hcomp : (fun x => InfiniteReflection.refl A (InfiniteReflection.refl B x))
      = InfiniteReflection.refl (fun i => A i || B i) := by
    funext x
    exact refl_comp A B x
  rw [hcomp]
  exact InfiniteReflectionASC.refl_filtrationCompat _

end InfiniteJoint

end MetaLang
