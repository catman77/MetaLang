import MetaLang.Congruence

/-!
# The observer and the legitimacy of a quotient

The second fundamental tenet of the corpus:

  `source ≠ observer`

The world need not consist of the objects an observer distinguishes. An
observer applies a readout `O : S → X`, and that readout is legitimate
**only if it preserves continuation structure**: it may glue together only
what no admissible future can tell apart.

Gauge invariance is proved here as well: renaming surface names — of states
or of responses — does not change the internal language. This is the formal
counterpart of gates `S24`/`S25` of v0.38, where every world underwent a
random renaming.
-/

namespace MetaLang

universe u

/-- An observer: a readout of source states into its own alphabet. -/
structure Observer (M : Machine) where
  /-- The observer's alphabet. -/
  X : Type u
  /-- Readout. -/
  obs : M.St → X

namespace Observer

variable {M : Machine} (O : Observer M)

/-- An observer **respects** semantics when it does not separate what is
semantically identical. -/
def Respects : Prop := ∀ s t : M.St, M.Indist s t → O.obs s = O.obs t

/-- An observer is **legitimate** when it does not glue states with
different continuation structure. This is the continuation-congruence
principle. -/
def Legitimate : Prop := ∀ s t : M.St, O.obs s = O.obs t → M.Indist s t

/-- A respecting observer **factors** through the internal language. -/
noncomputable def factor (h : O.Respects) : M.InternalLanguage → O.X :=
  Quotient.lift O.obs (fun s t hst => h s t hst)

@[simp] theorem factor_mk (h : O.Respects) (s : M.St) :
    O.factor h (Quotient.mk (Machine.indistSetoid M) s) = O.obs s := rfl

/-- Factorization exists exactly for respecting observers. -/
theorem respects_iff_factors :
    O.Respects ↔ ∃ g : M.InternalLanguage → O.X,
      ∀ s : M.St, g (Quotient.mk (Machine.indistSetoid M) s) = O.obs s := by
  constructor
  · intro h
    exact ⟨O.factor h, fun s => rfl⟩
  · rintro ⟨g, hg⟩ s t hst
    rw [← hg s, ← hg t]
    exact congrArg g (Quotient.sound hst)

/-- **Legitimacy criterion.** For a respecting observer, legitimacy is
equivalent to injectivity of the induced map on the internal language:
distinct words of the language must stay distinct for the observer. -/
theorem legitimate_iff_factor_injective (h : O.Respects) :
    O.Legitimate ↔ Function.Injective (O.factor h) := by
  constructor
  · intro hleg q₁ q₂ hq
    induction q₁ using Quotient.inductionOn with
    | h s =>
        induction q₂ using Quotient.inductionOn with
        | h t => exact Quotient.sound (hleg s t hq)
  · intro hinj s t hst
    exact Quotient.exact (hinj (show O.factor h _ = O.factor h _ from hst))

/-- The canonical projection onto the internal language is itself an
observer — and it is exactly the observer that glues nothing extra. -/
def canonical (M : Machine) : Observer M where
  X := M.InternalLanguage
  obs := fun s => Quotient.mk (Machine.indistSetoid M) s

theorem canonical_respects (M : Machine) : (canonical M).Respects :=
  fun _ _ h => Quotient.sound h

theorem canonical_legitimate (M : Machine) : (canonical M).Legitimate :=
  fun _ _ h => Quotient.exact h

end Observer

/-! ### Gauge invariance

Absolute names belong to the observer; relations survive a change of
observer. -/

/-- Renaming of source states along a bijection. -/
def Machine.relabel (M : Machine) {St' : Type u} (e : M.St ≃ St') : Machine where
  St := St'
  Act := M.Act
  Resp := M.Resp
  T := fun a s => e (M.T a (e.symm s))
  R := fun s => M.R (e.symm s)

namespace Machine

variable {M : Machine} {St' : Type u} (e : M.St ≃ St')

@[simp] theorem relabel_transport (w : List M.Act) (s : M.St) :
    (M.relabel e).transport w (e s) = e (M.transport w s) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
      have hstep : (M.relabel e).T a (e s) = e (M.T a s) := by
        show e (M.T a (e.symm (e s))) = e (M.T a s)
        rw [Equiv.symm_apply_apply]
      calc (M.relabel e).transport (a :: w) (e s)
          = (M.relabel e).transport w ((M.relabel e).T a (e s)) := rfl
        _ = (M.relabel e).transport w (e (M.T a s)) := by rw [hstep]
        _ = e (M.transport w (M.T a s)) := ih _
        _ = e (M.transport (a :: w) s) := rfl

/-- **Gauge invariance of the internal language.** Renaming states neither
creates nor destroys semantic distinctions. Surface names belong to the
observer, not to the source. -/
theorem indist_relabel_iff (s t : M.St) :
    (M.relabel e).Indist (e s) (e t) ↔ M.Indist s t := by
  constructor
  · intro h w
    have hw := h w
    rw [relabel_transport, relabel_transport] at hw
    show M.R (M.transport w s) = M.R (M.transport w t)
    have hs : (M.relabel e).R (e (M.transport w s)) = M.R (M.transport w s) := by
      show M.R (e.symm (e (M.transport w s))) = _
      rw [Equiv.symm_apply_apply]
    have ht : (M.relabel e).R (e (M.transport w t)) = M.R (M.transport w t) := by
      show M.R (e.symm (e (M.transport w t))) = _
      rw [Equiv.symm_apply_apply]
    rw [← hs, ← ht]; exact hw
  · intro h w
    rw [relabel_transport, relabel_transport]
    show M.R (e.symm (e (M.transport w s))) = M.R (e.symm (e (M.transport w t)))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact h w

/-- Renaming **responses** along an injection likewise leaves the language
unchanged: observable names carry no semantics by themselves. -/
def relabelResp (M : Machine) {Resp' : Type u} (f : M.Resp → Resp') : Machine where
  St := M.St
  Act := M.Act
  Resp := Resp'
  T := M.T
  R := fun s => f (M.R s)

theorem indist_relabelResp_iff {Resp' : Type u} {f : M.Resp → Resp'}
    (hf : Function.Injective f) (s t : M.St) :
    (M.relabelResp f).Indist s t ↔ M.Indist s t := by
  have htr : ∀ (w : List M.Act) (x : M.St),
      (M.relabelResp f).transport w x = M.transport w x := by
    intro w
    induction w with
    | nil => intro x; rfl
    | cons a w ih => intro x; exact ih (M.T a x)
  constructor
  · intro h w
    have hw := h w
    rw [htr, htr] at hw
    exact hf hw
  · intro h w
    rw [htr, htr]
    exact congrArg f (h w)

end Machine

end MetaLang
