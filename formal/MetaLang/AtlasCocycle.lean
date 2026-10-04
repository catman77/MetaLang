import MetaLang.MeaningWitnesses

/-!
# The gauge atlas: explicit transitions and the cocycle (v0.22 `S6`, `S7`)

`AlgebraicDescent.lean` proves descent of operations, but the cocycle law
there degenerates to transitivity of equality of presentations (downgrade
#29): the transitions `g_ij` themselves are never built as maps.

Here they are. If the presentations are bijective — which is exactly what
"full presentation" means in v0.22 §1 — the transition is defined as

  `g i j = pres_j⁻¹ ∘ pres_i`,

and then the cocycle law `g_jk ∘ g_ij = g_ik` holds on **maps**, not on
equalities of points. The second result: under algebraic compatibility of
the charts, every transition is a homomorphism of the signature — this is
gate `S7` of v0.22.

The second half of the file is v0.23 `S10`–`S12`: ASC continuity of `⊕`,
`⊖`, `ρ` **after globalization**. `MeaningAlgebra.lean` gives the continuity
theorem for an arbitrary filtration-compatible operation and
`AlgebraicDescent.lean` gives the gluing from a product atlas. Here the two
are joined on a concrete atlas with **partial** charts whose glued result is
the group operation of the shift machine.
-/

namespace MetaLang

universe u

/-! ## An atlas with bijective presentations -/

/-- A gauge atlas: the charts are full presentations of one and the same
semantic space, differing only by gauge. -/
structure GaugeAtlas (Q : Type u) where
  /-- Chart indices. -/
  ι : Type u
  /-- The atlas is nonempty. -/
  nonempty : Nonempty ι
  /-- Chart carriers. -/
  C : ι → Type u
  /-- Presentations. -/
  pres : ∀ i, C i → Q
  /-- "Full presentation" in the sense of v0.22 §1 — a bijection. -/
  pres_bij : ∀ i, Function.Bijective (pres i)
  /-- Local signatures. -/
  sig : ∀ i, Sig (C i)
  /-- Compatibility of synthesis on overlaps. -/
  compat_oplus : ∀ i j (a b : C i) (a' b' : C j),
    pres i a = pres j a' → pres i b = pres j b' →
    pres i ((sig i).oplus a b) = pres j ((sig j).oplus a' b')
  /-- Compatibility of contrast. -/
  compat_ominus : ∀ i j (a b : C i) (a' b' : C j),
    pres i a = pres j a' → pres i b = pres j b' →
    pres i ((sig i).ominus a b) = pres j ((sig j).ominus a' b')
  /-- Compatibility of reflection. -/
  compat_rho : ∀ i j (a : C i) (a' : C j),
    pres i a = pres j a' →
    pres i ((sig i).rho a) = pres j ((sig j).rho a')

namespace GaugeAtlas

variable {Q : Type u} (A : GaugeAtlas Q)

/-- A presentation as an equivalence. -/
noncomputable def chartEquiv (i : A.ι) : A.C i ≃ Q :=
  Equiv.ofBijective (A.pres i) (A.pres_bij i)

/-- The transition between charts: lift through `j` what `i` presents. -/
noncomputable def g (i j : A.ι) : A.C i → A.C j :=
  fun a => (A.chartEquiv j).symm (A.pres i a)

@[simp] theorem pres_g (i j : A.ι) (a : A.C i) : A.pres j (A.g i j a) = A.pres i a :=
  (A.chartEquiv j).apply_symm_apply (A.pres i a)

/-- The transition into itself is the identity. -/
@[simp] theorem g_self (i : A.ι) (a : A.C i) : A.g i i a = a :=
  (A.chartEquiv i).symm_apply_apply a

/-- **The cocycle law on transitions (gate `S6` of v0.22).** This is a claim
about maps, not about equality of points: the triple overlap is
coherent. -/
theorem g_cocycle (i j k : A.ι) (a : A.C i) : A.g j k (A.g i j a) = A.g i k a := by
  show (A.chartEquiv k).symm (A.pres j (A.g i j a)) = (A.chartEquiv k).symm (A.pres i a)
  rw [pres_g]

/-- The transitions are invertible. -/
theorem g_inv (i j : A.ι) (a : A.C i) : A.g j i (A.g i j a) = a := by
  rw [g_cocycle, g_self]

/-- **A transition is a homomorphism of the signature (gate `S7` of v0.22).** -/
theorem g_hom (i j : A.ι) : (A.sig i).Hom (A.sig j) (A.g i j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    refine (A.pres_bij j).1 ?_
    rw [pres_g]
    exact A.compat_oplus i j a b (A.g i j a) (A.g i j b) (by rw [pres_g]) (by rw [pres_g])
  · intro a b
    refine (A.pres_bij j).1 ?_
    rw [pres_g]
    exact A.compat_ominus i j a b (A.g i j a) (A.g i j b) (by rw [pres_g]) (by rw [pres_g])
  · intro a
    refine (A.pres_bij j).1 ?_
    rw [pres_g]
    exact A.compat_rho i j a (A.g i j a) (by rw [pres_g])

/-- A gauge atlas is a special case of an algebraic one. -/
def toAlgAtlas : AlgAtlas Q where
  ι := A.ι
  nonempty := A.nonempty
  C := A.C
  pres := A.pres
  pres_surj := fun i => (A.pres_bij i).2
  local_sig := A.sig
  compat_oplus := A.compat_oplus
  compat_ominus := A.compat_ominus
  compat_rho := A.compat_rho

end GaugeAtlas

/-! ## ASC continuity after globalization (v0.23 `S10`–`S12`) -/

namespace Globalized

open Witnesses Witnesses.GroupWitness

variable (G : Type) [Group G]

/-- Two **partial** charts on sequences: a neutral zeroth coordinate and
everything else. Together they cover the carrier, but neither covers it
alone. -/
def chartOf : Bool → Set (ℕ → G)
  | true => {x | x 0 = 1}
  | false => {x | x 0 ≠ 1}

theorem chart_covers (x : ℕ → G) : ∃ b, x ∈ chartOf G b := by
  by_cases h : x 0 = 1
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

/-- A product atlas whose local maps all specify the same operation. -/
def opAtlas (f : (ℕ → G) → (ℕ → G) → (ℕ → G)) : ProductAtlas (ℕ → G) where
  ι := Bool
  chart := chartOf G
  cell := fun _ _ => True
  mu := fun _ _ => f
  tuple_cover := fun x y => by
    obtain ⟨i, hi⟩ := chart_covers G x
    obtain ⟨j, hj⟩ := chart_covers G y
    exact ⟨i, j, trivial, hi, hj⟩
  overlap := by intros; rfl

theorem glue_opAtlas (f : (ℕ → G) → (ℕ → G) → (ℕ → G)) : (opAtlas G f).glue = f := by
  funext x y
  obtain ⟨i, hi⟩ := chart_covers G x
  obtain ⟨j, hj⟩ := chart_covers G y
  exact (opAtlas G f).glue_eq_local i j x y trivial hi hj

/-- An atlas for a unary operation over a cover of states. -/
def rhoAtlas (r : (ℕ → G) → (ℕ → G)) : UnaryAtlas (ℕ → G) where
  ι := Bool
  chart := chartOf G
  covers := chart_covers G
  r := fun _ => r
  overlap := by intros; rfl

theorem glue_rhoAtlas (r : (ℕ → G) → (ℕ → G)) : (rhoAtlas G r).glue = r := by
  funext x
  obtain ⟨i, hi⟩ := chart_covers G x
  exact (rhoAtlas G r).glue_eq_local i x hi

/-- **`⊕` is ASC-continuous after globalization (gate `S10` of v0.23).** -/
theorem gplus_continuous_after_globalization :
    (shiftMachine G).FiltrationCompat₂ (opAtlas G (gplus (G := G))).glue := by
  rw [glue_opAtlas]
  exact pointwise_filtrationCompat₂ (fun a b => a * b)

/-- **`⊖` is ASC-continuous after globalization (gate `S11` of v0.23).** -/
theorem gminus_continuous_after_globalization :
    (shiftMachine G).FiltrationCompat₂ (opAtlas G (gminus (G := G))).glue := by
  rw [glue_opAtlas]
  exact pointwise_filtrationCompat₂ (fun a b => a * b⁻¹)

/-- **`ρ` is ASC-continuous after globalization (gate `S12` of v0.23).** -/
theorem grho_continuous_after_globalization (h : G) :
    (shiftMachine G).FiltrationCompat₁ (rhoAtlas G (grho h)).glue := by
  rw [glue_rhoAtlas]
  exact pointwise_filtrationCompat₁ (fun a => h * a * h⁻¹)

/-- The real-valued form: the glued synthesis is 1-Lipschitz. -/
theorem gplus_lipschitz_after_globalization (x x' y y' : ℕ → G) :
    (shiftMachine G).dASC ((opAtlas G (gplus (G := G))).glue x y)
        ((opAtlas G (gplus (G := G))).glue x' y') ≤
      max ((shiftMachine G).dASC x x') ((shiftMachine G).dASC y y') :=
  Machine.dASC_op_le_max (gplus_continuous_after_globalization G) x x' y y'

end Globalized

end MetaLang
