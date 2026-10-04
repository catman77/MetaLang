import MetaLang.Congruence

/-!
# The observation diagram and the operational object

The abstract layer of v0.38. For a source `S` and a declared observation
class `Obs(S)` we define:

* the universal evaluation `η_S(s) = (O(s))_{O ∈ Obs}`;
* its kernel `ker η_S = ⋂_O ker O`;
* the operational object `S_op = S / ker η_S`;
* the subdirect embedding `η̄ : S_op → ∏_O X_O`.

This layer deliberately does not depend on `Machine`: it speaks about any
source with any declared family of observations. The link to the internal
language of M2 is a single theorem at the end of the file: `Indist` is
exactly the kernel of the family "response after a word of contexts". M2 and
M4 thereby turn out to be one construction.
-/

namespace MetaLang

universe u

/-- A declared family of observations on a source `S`. -/
structure ObsFamily (S : Type u) where
  /-- Observer index. -/
  ι : Type u
  /-- Value alphabet of each observer. -/
  X : ι → Type u
  /-- The readout itself. -/
  O : ∀ i : ι, S → X i

namespace ObsFamily

variable {S : Type u} (F : ObsFamily S)

/-- The universal evaluation `η`. -/
def eta (s : S) : ∀ i : F.ι, F.X i := fun i => F.O i s

/-- The kernel of the family: indistinguishability by **all** declared observations. -/
def Ker (s t : S) : Prop := ∀ i : F.ι, F.O i s = F.O i t

variable {F}

theorem ker_refl (s : S) : F.Ker s s := fun _ => rfl

theorem ker_symm {s t : S} (h : F.Ker s t) : F.Ker t s := fun i => (h i).symm

theorem ker_trans {s t r : S} (h₁ : F.Ker s t) (h₂ : F.Ker t r) : F.Ker s r :=
  fun i => (h₁ i).trans (h₂ i)

theorem ker_equivalence (F : ObsFamily S) : Equivalence F.Ker :=
  ⟨ker_refl, ker_symm, ker_trans⟩

/-- `ker η = ⋂_O ker O` — the kernel of the evaluation is the intersection
of the observer kernels. In this encoding the equality holds by
definition. -/
theorem ker_iff_eta_eq (s t : S) : F.Ker s t ↔ F.eta s = F.eta t := by
  constructor
  · intro h; funext i; exact h i
  · intro h i; exact congrFun h i

theorem ker_iff_forall_ker (s t : S) :
    F.Ker s t ↔ ∀ i : F.ι, F.O i s = F.O i t := Iff.rfl

/-- The equivalence relation that defines the operational object. -/
def opSetoid (F : ObsFamily S) : Setoid S := ⟨F.Ker, ker_equivalence F⟩

/-- `S_op = S / ker η` — the operational object. -/
def OpObject (F : ObsFamily S) : Type u := Quotient (opSetoid F)

/-- The canonical projection of the source onto the operational object. -/
def toOp (F : ObsFamily S) (s : S) : F.OpObject := Quotient.mk (opSetoid F) s

/-- The evaluation descends to the operational object. -/
def etaBar (F : ObsFamily S) : F.OpObject → (∀ i : F.ι, F.X i) :=
  Quotient.lift F.eta (fun _ _ h => (ker_iff_eta_eq _ _).mp h)

@[simp] theorem etaBar_toOp (s : S) : F.etaBar (F.toOp s) = F.eta s := rfl

/-- **Subdirect embedding.** The induced map from the operational object
into the product of observations is injective: `S_op` is exactly the part of
the source that the observations separate. -/
theorem etaBar_injective (F : ObsFamily S) : Function.Injective F.etaBar := by
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn with
  | h s =>
      induction q₂ using Quotient.inductionOn with
      | h t => exact Quotient.sound ((ker_iff_eta_eq s t).mpr h)

/-- The projection onto the operational object is surjective. -/
theorem toOp_surjective (F : ObsFamily S) : Function.Surjective F.toOp := by
  intro q
  induction q using Quotient.inductionOn with
  | h s => exact ⟨s, rfl⟩

/-- A source is **faithful** with respect to the family when the
observations separate everything: then the projection onto the operational
object is injective. -/
def Faithful (F : ObsFamily S) : Prop := ∀ s t : S, F.Ker s t → s = t

theorem toOp_injective_of_faithful (h : F.Faithful) : Function.Injective F.toOp := by
  intro s t hst
  exact h s t (Quotient.exact hst)

end ObsFamily

/-! ### Bridge to the internal language

The semantic quotient of M2 is a special case of the operational object: the
observations are "response after a word of contexts". -/

namespace Machine

variable (M : Machine)

/-- The observation family indexed by words of contexts. -/
def wordFamily : ObsFamily M.St where
  ι := List M.Act
  X := fun _ => M.Resp
  O := fun w s => M.R (M.transport w s)

/-- **The internal language is the operational object.** Indistinguishability
by continuations is exactly the kernel of the observation family "response
after a word". M2 and M4 describe one construction from two sides. -/
theorem indist_iff_wordFamily_ker (s t : M.St) :
    M.Indist s t ↔ (M.wordFamily).Ker s t := Iff.rfl

end Machine

end MetaLang
