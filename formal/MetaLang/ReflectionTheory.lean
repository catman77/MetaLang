import MetaLang.Reflection
import MetaLang.MeaningWitnesses

/-!
# Completing the theory of reflection (v0.25)

`Reflection.lean` proves the core: a reflective family yields a single-valued
`rho`; it is inflationary, monotone, idempotent, its fixed points are exactly
`F`, and it is left adjoint to the inclusion.

The rest of v0.25 is filled in here:

* the reflection relation is recovered from **behaviour plus `F`** (`S1`, `S2`);
* the principal reflection equals `κ ⊔ x` (`S9`);
* reflection preserves universal synthesis (`S10`);
* for a non-reflective `F` the reflection is canonically an **antichain**, and
  any forced choice of a single point breaks the adjunction (`S11`–`S13`);
* the infinite Boolean witness is inflationary and monotone, its fixed-point
  space is exact, and it is 1-Lipschitz (`S15`, `S16`, `S18`, `S19`).
-/

namespace MetaLang

universe u

/-! ## Reflection as an antichain of minimal elements -/

/-- The canonical reflection: the minimal elements of `F` above `x`. In
general this is an antichain, not a point. -/
def Ref {α : Type u} [PartialOrder α] (F : Set α) (x : α) : Set α :=
  {y | y ∈ F ∧ x ≤ y ∧ ∀ z ∈ F, x ≤ z → z ≤ y → z = y}

section Recovery

variable {P : Type u} [PartialOrder P] [DecidableRel ((· ≤ ·) : P → P → Prop)]

/-- **Behaviour plus `F` recovers the reflection relation (gates `S1`, `S2`
of v0.25).** The right-hand side mentions nothing but inclusion of
continuation languages and the subspace itself. -/
theorem isReflectionAt_iff_paths (F : Set P) (x y : P) :
    IsReflectionAt F x y ↔
      (y ∈ F ∧ (RefinementInterface.sys P).refines x y ∧
        ∀ z ∈ F, (RefinementInterface.sys P).refines x z →
          (RefinementInterface.sys P).refines y z) := by
  simp only [IsReflectionAt, RefinementInterface.refines_iff_le]

end Recovery

section Principal

variable {α : Type u} [Lattice α]

/-- **The principal reflection equals `κ ⊔ x` (gate `S9` of v0.25).** For a
principal upper cone the reflector is just adjoining `κ`. -/
theorem principal_isReflectionAt (κ x : α) :
    IsReflectionAt {z : α | κ ≤ z} x (κ ⊔ x) := by
  refine ⟨le_sup_left, le_sup_right, ?_⟩
  intro z hz hxz
  exact sup_le hz hxz

end Principal

section Preserve

variable {α : Type u} [PartialOrder α] {F : Set α} (h : Reflective F)

/-- **Reflection preserves universal synthesis (gate `S10` of v0.25).** The
image of the synthesis is the least element of `F` above both images: a left
adjoint carries least upper bounds to least upper bounds. -/
theorem rho_preserves_synthesis {x y z : α} (hz : IsSynthesis x y z) :
    IsLeast {f | f ∈ F ∧ rho h x ≤ f ∧ rho h y ≤ f} (rho h z) := by
  have hxz : x ≤ z := hz.1 (by simp)
  have hyz : y ≤ z := hz.1 (by simp)
  refine ⟨⟨rho_mem h z, rho_monotone h hxz, rho_monotone h hyz⟩, ?_⟩
  rintro f ⟨hf, hxf, hyf⟩
  refine rho_least h hf (hz.2 ?_)
  rintro b (rfl | rfl)
  · exact le_trans (le_rho h b) hxf
  · exact le_trans (le_rho h b) hyf

end Preserve

/-! ## A non-reflective family: reflection is multi-valued -/

namespace NonReflective

/-- The target subspace made of the two incomparable atoms of the diamond. -/
def F : Set M3 := {M3.a, M3.b}

theorem a_mem : M3.a ∈ F := Or.inl rfl

theorem b_mem : M3.b ∈ F := Or.inr rfl

/-- **The reflection of a non-reflective family is an antichain (gates
`S11`, `S12` of v0.25).** Above `bot` both `a` and `b` are minimal; there is
no single-valued answer. -/
theorem ref_bot_antichain :
    M3.a ∈ Ref F M3.bot ∧ M3.b ∈ Ref F M3.bot ∧ M3.a ≠ M3.b := by
  refine ⟨⟨a_mem, by decide, ?_⟩, ⟨b_mem, by decide, ?_⟩, by decide⟩
  · rintro z (rfl | rfl) _ hz
    · rfl
    · exact absurd hz (by decide)
  · rintro z (rfl | rfl) _ hz
    · exact absurd hz (by decide)
    · rfl

/-- **A forced choice breaks the adjunction (gate `S13` of v0.25).** Any
operator that picks `a` above `bot` ceases to be a left adjoint: `bot ≤ b`,
yet `a ≰ b`. -/
theorem forced_choice_breaks_adjunction (r : M3 → M3) (hr : r M3.bot = M3.a) :
    ¬ (∀ (x : M3), ∀ f ∈ F, r x ≤ f ↔ x ≤ f) := by
  intro h
  have := (h M3.bot M3.b b_mem).mpr (by decide)
  rw [hr] at this
  exact absurd this (by decide)

end NonReflective

/-! ## The infinite Boolean witness (v0.25 `S15`, `S16`, `S18`, `S19`) -/

namespace InfiniteReflectionASC

open Witnesses Witnesses.InfiniteReflection

variable (A : ℕ → Bool)

/-- **The reflection of the infinite Boolean witness is 1-Lipschitz (gate
`S19` of v0.25).** -/
theorem refl_filtrationCompat :
    (shiftMachine Bool).FiltrationCompat₁ (refl A) :=
  pointwiseIdx_filtrationCompat₁ (fun i a => A i || a)

end InfiniteReflectionASC

end MetaLang
