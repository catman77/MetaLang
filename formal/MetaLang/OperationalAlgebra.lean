import MetaLang.MultiObserver

/-!
# The equational theory of the operational object (v0.35–v0.38)

The closing of the third checkpoint of the meaning algebra.

`ObservationDiagram.lean` builds `S_op = S / ⋂ ker O` as a **set**. Here an
algebra appears on it: since every observer is a homomorphism, the joint
kernel is automatically a congruence, and the operations of the source
descend to `S_op` in a unique way.

The main result (v0.37 §4):

  `S_op ⊨ t = u` ⟺ `every observed world ⊨ t = u`.

Hence the two sides of the corpus's conclusion. For a jointly faithful
family, the theory of the source is exactly the intersection of the
observers' theories. For a non-faithful one, the observers reconstruct
`S_op` and **not** `S`: equations false in the source may hold in the
operational object. The shadow witness of `MultiObserver.lean` exhibits such
an equation explicitly.
-/

namespace MetaLang

universe u

namespace AlgObsFamily

variable {S : Type u} (F : AlgObsFamily S)

/-! ## The operational object as an algebra -/

theorem ker_equivalence : Equivalence F.Ker where
  refl _ := fun _ => rfl
  symm h := fun i => (h i).symm
  trans h₁ h₂ := fun i => (h₁ i).trans (h₂ i)

/-- The joint kernel as an equivalence relation. -/
def opSetoid : Setoid S := ⟨F.Ker, ker_equivalence F⟩

/-- The operational object: the source modulo the joint kernel. -/
def OpObject : Type u := Quotient F.opSetoid

/-- The canonical projection onto the operational object. -/
def toOp (x : S) : F.OpObject := Quotient.mk F.opSetoid x

theorem toOp_surjective : Function.Surjective F.toOp := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨x, rfl⟩

theorem toOp_eq_iff (x y : S) : F.toOp x = F.toOp y ↔ F.Ker x y := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- The joint kernel of an algebraic family coincides with the kernel of the
underlying `ObsFamily` — the algebraic superstructure changes nothing in the
set-level part of `ObservationDiagram.lean`. -/
theorem ker_eq_obsFamily_ker (x y : S) : F.Ker x y ↔ F.toObsFamily.Ker x y :=
  Iff.rfl

/-- The kernel is a congruence for a binary operation: an immediate
consequence of every observer being a homomorphism. -/
theorem ker_congr₂ (μ : S → S → S)
    (hμ : ∀ i, ∀ x y : S, F.O i (μ x y) = (F.sigW i).oplus (F.O i x) (F.O i y))
    {a₁ a₂ b₁ b₂ : S} (ha : F.Ker a₁ a₂) (hb : F.Ker b₁ b₂) :
    F.Ker (μ a₁ b₁) (μ a₂ b₂) := by
  intro i
  rw [hμ i, hμ i, ha i, hb i]

/-- The algebra on the operational object. -/
def opSig : Sig F.OpObject where
  oplus := Quotient.lift₂ (fun a b => F.toOp (F.sigS.oplus a b)) (by
    intro a₁ b₁ a₂ b₂ ha hb
    exact Quotient.sound fun i => by
      rw [(F.hom i).1, (F.hom i).1, ha i, hb i])
  ominus := Quotient.lift₂ (fun a b => F.toOp (F.sigS.ominus a b)) (by
    intro a₁ b₁ a₂ b₂ ha hb
    exact Quotient.sound fun i => by
      rw [(F.hom i).2.1, (F.hom i).2.1, ha i, hb i])
  rho := Quotient.lift (fun a => F.toOp (F.sigS.rho a)) (by
    intro a₁ a₂ ha
    exact Quotient.sound fun i => by
      rw [(F.hom i).2.2, (F.hom i).2.2, ha i])

/-- **The operational quotient inherits the operation (gates `S20` of v0.35,
`S28` of v0.36).** The canonical projection is a homomorphism of the
signature. -/
theorem toOp_hom : F.sigS.Hom F.opSig F.toOp :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- **Associativity of the source is preserved (gates `S21` of v0.35, `S29`
of v0.36).** -/
theorem opSig_assoc
    (hA : ∀ x y z : S, F.sigS.oplus (F.sigS.oplus x y) z =
      F.sigS.oplus x (F.sigS.oplus y z)) :
    ∀ a b c : F.OpObject, F.opSig.oplus (F.opSig.oplus a b) c =
      F.opSig.oplus a (F.opSig.oplus b c) :=
  Projection.assoc_descends F.toOp_hom F.toOp_surjective hA

/-! ## Observers as homomorphisms of the operational object -/

/-- An observer factored through the operational object. -/
def opO (i : F.ι) : F.OpObject → F.X i :=
  Quotient.lift (F.O i) (fun _ _ h => h i)

@[simp] theorem opO_toOp (i : F.ι) (x : S) : F.opO i (F.toOp x) = F.O i x := rfl

theorem opO_surjective (i : F.ι) : Function.Surjective (F.opO i) := by
  intro w
  obtain ⟨x, hx⟩ := F.surj i w
  exact ⟨F.toOp x, hx⟩

theorem opO_hom (i : F.ι) : F.opSig.Hom (F.sigW i) (F.opO i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    induction a using Quotient.inductionOn with
    | _ x =>
      induction b using Quotient.inductionOn with
      | _ y => exact (F.hom i).1 x y
  · intro a b
    induction a using Quotient.inductionOn with
    | _ x =>
      induction b using Quotient.inductionOn with
      | _ y => exact (F.hom i).2.1 x y
  · intro a
    induction a using Quotient.inductionOn with
    | _ x => exact (F.hom i).2.2 x

/-- A composite of signature homomorphisms is a homomorphism (gate `S5` of v0.37). -/
theorem Sig.Hom.comp {α β γ : Type u} {A : Sig α} {B : Sig β} {C : Sig γ}
    {f : α → β} {g : β → γ} (hf : A.Hom B f) (hg : B.Hom C g) :
    A.Hom C (g ∘ f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    show g (f (A.oplus x y)) = C.oplus (g (f x)) (g (f y))
    rw [hf.1, hg.1]
  · intro x y
    show g (f (A.ominus x y)) = C.ominus (g (f x)) (g (f y))
    rw [hf.2.1, hg.2.1]
  · intro x
    show g (f (A.rho x)) = C.rho (g (f x))
    rw [hf.2.2, hg.2.2]

/-- The signature on the product of the observed worlds: componentwise operations. -/
def prodSig : Sig (∀ i : F.ι, F.X i) where
  oplus := fun p q i => (F.sigW i).oplus (p i) (q i)
  ominus := fun p q i => (F.sigW i).ominus (p i) (q i)
  rho := fun p i => (F.sigW i).rho (p i)

/-- The evaluation of the operational object into the product. -/
def evalProd : F.OpObject → (∀ i : F.ι, F.X i) := fun q i => F.opO i q

/-- **The evaluation is a homomorphism into the product (gate `S9` of v0.37).** -/
theorem evalProd_hom : F.opSig.Hom F.prodSig F.evalProd := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    funext i
    exact (F.opO_hom i).1 a b
  · intro a b
    funext i
    exact (F.opO_hom i).2.1 a b
  · intro a
    funext i
    exact (F.opO_hom i).2.2 a

/-- **The evaluation is injective: the image is subdirect (gates `S8`, `S10` of v0.37).** -/
theorem evalProd_injective : Function.Injective F.evalProd := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      refine Quotient.sound fun i => ?_
      exact congrFun hab i

/-- **Faithfulness is equivalent to triviality of the universal kernel
(gate `S31` of v0.37).** -/
theorem faithful_iff_toOp_injective : F.Faithful ↔ Function.Injective F.toOp := by
  constructor
  · intro h x y hxy
    exact h x y (Quotient.exact hxy)
  · intro h x y hker
    exact h (Quotient.sound hker)

/-! ## The equational theory of `S_op` -/

/-- The equation holds in the operational object. -/
def HoldsOp {V : Type u} (F : AlgObsFamily S) (t u : Term V) : Prop :=
  ∀ τ : V → F.OpObject, Term.eval F.opSig τ t = Term.eval F.opSig τ u

open scoped Classical in
/-- **The equational reconstruction theorem (v0.37 §4, gates `S11` of v0.37,
`S15` of v0.38).** The equational theory of the operational object coincides
exactly with the common theory of all the observers. -/
theorem holdsOp_iff_forall_holdsW {V : Type u} (t u : Term V) :
    F.HoldsOp t u ↔ ∀ i, F.HoldsW i t u := by
  constructor
  · intro h i
    exact law_descends (F.opO_hom i) (F.opO_surjective i) h
  · intro h τ
    have hσ : ∃ σ : V → S, F.toOp ∘ σ = τ := by
      refine ⟨fun v => Classical.choose (F.toOp_surjective (τ v)), ?_⟩
      funext v
      exact Classical.choose_spec (F.toOp_surjective (τ v))
    obtain ⟨σ, rfl⟩ := hσ
    rw [← Term.eval_hom F.toOp_hom σ t, ← Term.eval_hom F.toOp_hom σ u]
    refine Quotient.sound fun i => ?_
    rw [Term.eval_hom (F.hom i) σ t, Term.eval_hom (F.hom i) σ u]
    exact h i (F.O i ∘ σ)

/-- **For a jointly faithful family, `S_op` is the source itself as far as
equations are concerned.** The theory of the source is the intersection of
the observers' theories. -/
theorem holdsOp_iff_holdsS (hf : F.Faithful) {V : Type u} (t u : Term V) :
    F.HoldsOp t u ↔ F.HoldsS t u :=
  (F.holdsOp_iff_forall_holdsW t u).trans (joint_reconstruction hf t u)

/-- **The shadow lives in `S_op` (gate `S40` of v0.38).** An equation true
for every observer is true in the operational object as well — regardless of
whether it holds in the source. Observation reconstructs `S_op`, not `S`. -/
theorem holdsOp_of_scoped {V : Type u} {t u : Term V} (h : F.Scoped t u) :
    F.HoldsOp t u :=
  (F.holdsOp_iff_forall_holdsW t u).mpr h

end AlgObsFamily

/-! ## The witness: `S_op` satisfies an equation false in the source -/

namespace ShadowWitness

/-- **Observers reconstruct `S_op`, not `S`.** Commutativity holds in the
operational object of the sign family and fails in the source. This is not an
error of science: `S_op` is precisely its terminal object. -/
theorem opObject_commutative_source_not :
    shadowFamily.HoldsOp commT commU ∧ ¬ shadowFamily.HoldsS commT commU :=
  ⟨shadowFamily.holdsOp_of_scoped shadow_scoped, shadow_not_fundamental⟩

/-- The extended family is jointly faithful, so its operational object
already rejects the shadow. -/
theorem active_opObject_refutes :
    ¬ activeFamily.HoldsOp commT commU := by
  intro h
  exact active_refutes_shadow ((activeFamily.holdsOp_iff_forall_holdsW commT commU).mp h)

end ShadowWitness

end MetaLang
