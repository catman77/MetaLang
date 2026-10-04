import MetaLang.Observer
import MetaLang.InternalLanguage

/-!
# Singularity as loss of continuation information

  `singularity = loss of continuation information under observation`

Sometimes an observer map glues source states whose futures differ. At that
place a "hole" appears in the observer's language: an ambiguity, a `0`, an
`∞`, a branch point. The corpus proposes not to discard such differences but
to keep the fibre `O⁻¹(x)`.

Here that is proved literally: an observer augmented with its fibre recovers
exactly the distinction the original observer was losing.
-/

namespace MetaLang

namespace Observer

variable {M : Machine} (O : Observer M)

/-- **An observational singularity**: the readout identified states whose
admissible continuations differ. -/
def Singular (s t : M.St) : Prop := O.obs s = O.obs t ∧ ¬ M.Indist s t

theorem not_legitimate_of_singular {s t : M.St} (h : O.Singular s t) :
    ¬ O.Legitimate := fun hleg => h.2 (hleg s t h.1)

/-- Legitimacy is exactly the absence of singularities. -/
theorem legitimate_iff_no_singular :
    O.Legitimate ↔ ∀ s t : M.St, ¬ O.Singular s t := by
  constructor
  · intro hleg s t hsing
    exact hsing.2 (hleg s t hsing.1)
  · intro hno s t hst
    by_contra hind
    exact hno s t ⟨hst, hind⟩

/-- The observation fibre over a value `x` — what the observer cannot tell apart. -/
def fibre (x : O.X) : Set M.St := {s | O.obs s = x}

theorem mem_fibre_self (s : M.St) : s ∈ O.fibre (O.obs s) := rfl

/-- States glued by a singularity lie in one fibre. -/
theorem singular_mem_fibre {s t : M.St} (h : O.Singular s t) :
    t ∈ O.fibre (O.obs s) := h.1.symm

/-- The lost distinction does not vanish: it has a finite witness. -/
theorem exists_witness_of_singular {s t : M.St} (h : O.Singular s t) :
    ∃ w : List M.Act, M.R (M.transport w s) ≠ M.R (M.transport w t) :=
  Machine.exists_witness_of_not_indist h.2

/-! ### Keeping the fibre -/

/-- The fibre-keeping observer: the semantic class of the state is added to
the surface value. -/
def withFibre : Observer M where
  X := O.X × M.InternalLanguage
  obs := fun s => (O.obs s, Quotient.mk (Machine.indistSetoid M) s)

/-- The fibre-keeping observer is always legitimate: it glues nothing extra. -/
theorem withFibre_legitimate : O.withFibre.Legitimate := by
  intro s t h
  exact Quotient.exact (congrArg Prod.snd h)

/-- **Keeping the fibre recovers the lost distinction.** Exactly the pair on
which the original observer had a singularity is separated by the
fibre-keeping observer. -/
theorem withFibre_recovers {s t : M.St} (h : O.Singular s t) :
    O.withFibre.obs s ≠ O.withFibre.obs t := by
  intro hEq
  exact h.2 (Quotient.exact (congrArg Prod.snd hEq))

/-- The fibre-keeping observer does not lose the surface information either. -/
theorem withFibre_refines (s t : M.St) (h : O.withFibre.obs s = O.withFibre.obs t) :
    O.obs s = O.obs t := congrArg Prod.fst h

end Observer

/-! ### A concrete singularity

An observer that sees only the immediate response is singular on the latent
distinction of v0.13: it glues states that diverge after two steps. -/

/-- The observer that reads only the immediate response. -/
def immediateObserver (M : Machine) : Observer M where
  X := M.Resp
  obs := M.R

/-- The immediate observer has a singularity on the latent pair. -/
theorem immediate_singular_on_latent :
    (immediateObserver latentMachine).Singular 0 1 :=
  ⟨latent_immediate_eq, immediateEffectNotSemantic.2.2⟩

/-- It is therefore not legitimate as a quotient of the source. -/
theorem immediate_not_legitimate :
    ¬ (immediateObserver latentMachine).Legitimate :=
  Observer.not_legitimate_of_singular _ immediate_singular_on_latent

/-- Augmented with the fibre, it does separate the lost pair. -/
theorem immediate_withFibre_recovers :
    (immediateObserver latentMachine).withFibre.obs 0
      ≠ (immediateObserver latentMachine).withFibre.obs 1 :=
  Observer.withFibre_recovers _ immediate_singular_on_latent

end MetaLang
