import Mathlib

/-!
# The continuation core

Formalization of the base object of the WORLD-META corpus:

  `C(h) = { x | hx is an admissible continuation }`

A world is given not by a set of objects and their properties, but by the
structure of admissible continuations.

## Representation convention for histories

A history is stored **in reverse order**: the head of the list is the most
recent event. So the prose `hx` ("history `h` extended by the symbol `x`")
is encoded as `x :: h`. This is a purely representational choice: it makes
`Adm` structurally recursive and induction over histories trivial. The
"earlier than" order then becomes the suffix relation `h <:+ k`, for which
Mathlib already supplies a partial order.

Everything in this file is defined through the single primitive `Step`;
admissibility `Adm` is **derived** from it rather than postulated. That is
why prefix closure below is a theorem, not an axiom.
-/

namespace MetaLang

universe u

/-- The frozen vocabulary of a continuation world.

The only primitive is `Step h x`: "after the realized history `h`, the
symbol `x` is admissible". Everything else is derived. -/
structure World where
  /-- Alphabet of distinctions. -/
  Sym : Type u
  /-- The admissible one-step continuation relation. -/
  Step : List Sym → Sym → Prop

namespace World

variable {W : World}

/-- An admissible history: the empty history is admissible, and every
admissible step out of an admissible history yields an admissible
history. -/
inductive Adm (W : World) : List W.Sym → Prop
  | nil : Adm W []
  | step {h : List W.Sym} {x : W.Sym} : Adm W h → W.Step h x → Adm W (x :: h)

/-- The continuation space `C(h)` — the fundamental object of the theory. -/
def C (W : World) (h : List W.Sym) : Set W.Sym := {x | W.Step h x}

/-- The "earlier than" relation: `h` is a realized prefix of the history `k`.

`time = order of continuation` — no numeric time is introduced at all. -/
def Precedes (W : World) (h k : List W.Sym) : Prop := h <:+ k

/-- The future cone: all admissible histories extending `h`. -/
def Cone (W : World) (h : List W.Sym) : Set (List W.Sym) :=
  {k | Adm W k ∧ W.Precedes h k}

end World

namespace World

variable {W : World}

/-! ### The continuation order -/

theorem precedes_refl (h : List W.Sym) : W.Precedes h h :=
  List.suffix_refl h

theorem precedes_trans {h k l : List W.Sym}
    (hk : W.Precedes h k) (kl : W.Precedes k l) : W.Precedes h l :=
  List.IsSuffix.trans hk kl

theorem precedes_antisymm {h k : List W.Sym}
    (hk : W.Precedes h k) (kh : W.Precedes k h) : h = k :=
  List.Sublist.antisymm hk.sublist kh.sublist

theorem precedes_extend (h : List W.Sym) (x : W.Sym) : W.Precedes h (x :: h) :=
  ⟨[x], rfl⟩

/-! ### Admissibility -/

/-- Constructor inversion: the tail of an admissible history is admissible. -/
theorem adm_tail {h : List W.Sym} {x : W.Sym} (ha : Adm W (x :: h)) : Adm W h := by
  cases ha with
  | step hh _ => exact hh

/-- The last step of an admissible history was an admissible step. -/
theorem step_of_adm {h : List W.Sym} {x : W.Sym} (ha : Adm W (x :: h)) : W.Step h x := by
  cases ha with
  | step _ hs => exact hs

/-- **Prefix closure.** Every realized part of an admissible history is
itself admissible. This is a theorem, not an axiom: it follows from
admissibility having been built up step by step. -/
theorem adm_of_precedes {h k : List W.Sym}
    (hk : Adm W k) (hp : W.Precedes h k) : Adm W h := by
  obtain ⟨t, rfl⟩ := hp
  induction t with
  | nil => simpa using hk
  | cons y t ih =>
      apply ih
      simpa using adm_tail hk

/-- Characterization: relative to an admissible history, a continuation is
admissible exactly when it lies in `C(h)`. -/
theorem adm_extend_iff {h : List W.Sym} (ha : Adm W h) (x : W.Sym) :
    Adm W (x :: h) ↔ x ∈ W.C h := by
  constructor
  · intro hx; exact step_of_adm hx
  · intro hx; exact Adm.step ha hx

/-! ### The future cone -/

/-- The cone narrows as the history grows: every future of a longer history
is a future of a shorter one. -/
theorem cone_mono {h k : List W.Sym} (hp : W.Precedes h k) :
    W.Cone k ⊆ W.Cone h := by
  rintro l ⟨hl, hkl⟩
  exact ⟨hl, precedes_trans hp hkl⟩

theorem cone_extend_subset (h : List W.Sym) (x : W.Sym) :
    W.Cone (x :: h) ⊆ W.Cone h :=
  cone_mono (precedes_extend h x)

theorem self_mem_cone {h : List W.Sym} (ha : Adm W h) : h ∈ W.Cone h :=
  ⟨ha, precedes_refl h⟩

/-! ### Meaning as a transformation of continuations

`meaning ≈ effect on continuations`. A sign means nothing on its own; its
meaning is how it changes the structure of admissible continuations. -/

/-- The effect of the symbol `x` in the context `h`: the continuation space
after it. -/
def Effect (W : World) (h : List W.Sym) (x : W.Sym) : Set W.Sym := W.C (x :: h)

/-- Two signs are equivalent when, in every admissible context, they produce
the same change of continuation structure. -/
def SignEquiv (W : World) (x y : W.Sym) : Prop :=
  ∀ h : List W.Sym, Adm W h → W.Effect h x = W.Effect h y

theorem signEquiv_refl (x : W.Sym) : W.SignEquiv x x := fun _ _ => rfl

theorem signEquiv_symm {x y : W.Sym} (h : W.SignEquiv x y) : W.SignEquiv y x :=
  fun k hk => (h k hk).symm

theorem signEquiv_trans {x y z : W.Sym}
    (hxy : W.SignEquiv x y) (hyz : W.SignEquiv y z) : W.SignEquiv x z :=
  fun k hk => (hxy k hk).trans (hyz k hk)

theorem signEquiv_equivalence (W : World) : Equivalence W.SignEquiv :=
  ⟨signEquiv_refl, signEquiv_symm, signEquiv_trans⟩

/-! ### Continuation filters

An axiom, a law, a rule, an observation — none of these is a predicate
valued `True`; each is a narrowing of the continuation space. -/

/-- A continuation filter: a context-dependent narrowing. -/
structure ContFilter (W : World) where
  /-- How the filter acts in the context of a history. -/
  restrict : List W.Sym → Set W.Sym → Set W.Sym
  /-- A filter only narrows: it never creates new continuations. -/
  restrict_le : ∀ (h : List W.Sym) (S : Set W.Sym), restrict h S ⊆ S

namespace ContFilter

variable (F : ContFilter W)

/-- The filtered continuation space stays inside the original one. -/
theorem filtered_subset (h : List W.Sym) : F.restrict h (W.C h) ⊆ W.C h :=
  F.restrict_le h (W.C h)

/-- Admissibility survives filtering. -/
theorem adm_of_filtered {h : List W.Sym} {x : W.Sym}
    (ha : Adm W h) (hx : x ∈ F.restrict h (W.C h)) : Adm W (x :: h) :=
  (adm_extend_iff ha x).mpr (F.filtered_subset h hx)

end ContFilter

end World

end MetaLang
