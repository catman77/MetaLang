import MetaLang.Continuation

/-!
# The semantic quotient

The central construction of the corpus for v0.6–v0.15:

  `s ≡ t  ⟺  no admissible future interaction distinguishes s from t`

The formalization uses a machine `(St, Act, Resp, T, R)`: source states,
admissible contextual transports, observer responses. Two objects are
defined —

* `Indist` — the direct definition through all context words;
* `approx n` — iterative refinement of the partition (the Moore /
  Myhill–Nerode analogue);

and they are proved to coincide on a finite state set, the limit being the
**greatest** context congruence that does not glue distinguishable
responses.

The reading matters: what is minimized is not an automaton but the source
`S`, and the right-hand relation says "no admissible future distinction has
been lost".
-/

namespace MetaLang

universe u

/-- A source with admissible contextual transports and an observer response. -/
structure Machine where
  /-- Source states. -/
  St : Type u
  /-- Admissible contextual transports. -/
  Act : Type u
  /-- Observable responses. -/
  Resp : Type u
  /-- The contextual transport. -/
  T : Act → St → St
  /-- Materialization / response. -/
  R : St → Resp

namespace Machine

variable (M : Machine)

/-- Transport along a word of contexts, left to right. -/
def transport : List M.Act → M.St → M.St
  | [], s => s
  | a :: w, s => transport w (M.T a s)

@[simp] theorem transport_nil (s : M.St) : M.transport [] s = s := rfl

@[simp] theorem transport_cons (a : M.Act) (w : List M.Act) (s : M.St) :
    M.transport (a :: w) s = M.transport w (M.T a s) := rfl

/-- **Indistinguishability by continuations.** The direct definition of the
internal language: `s` and `t` are the same word when no admissible future
separates them. -/
def Indist (s t : M.St) : Prop :=
  ∀ w : List M.Act, M.R (M.transport w s) = M.R (M.transport w t)

/-- Iterative refinement: indistinguishability at depth `n`. -/
def approx : ℕ → M.St → M.St → Prop
  | 0, s, t => M.R s = M.R t
  | n + 1, s, t => M.R s = M.R t ∧ ∀ a : M.Act, approx n (M.T a s) (M.T a t)

variable {M}

/-! ### Basic properties -/

theorem indist_refl (s : M.St) : M.Indist s s := fun _ => rfl

theorem indist_symm {s t : M.St} (h : M.Indist s t) : M.Indist t s :=
  fun w => (h w).symm

theorem indist_trans {s t r : M.St} (hst : M.Indist s t) (htr : M.Indist t r) :
    M.Indist s r := fun w => (hst w).trans (htr w)

theorem indist_equivalence (M : Machine) : Equivalence M.Indist :=
  ⟨indist_refl, indist_symm, indist_trans⟩

/-- Indistinguishable states give the same immediate response. -/
theorem indist_resp {s t : M.St} (h : M.Indist s t) : M.R s = M.R t := h []

/-- **Congruence.** Indistinguishability is preserved by every contextual
transport: a context cannot create a distinction where there was none. -/
theorem indist_congr {s t : M.St} (h : M.Indist s t) (a : M.Act) :
    M.Indist (M.T a s) (M.T a t) := fun w => h (a :: w)

/-- **A constructive witness of difference.** If two states are not
equivalent, there is a finite word of contexts after which the responses
diverge. A distinction is always exhibitable, never merely postulated. -/
theorem exists_witness_of_not_indist {s t : M.St} (h : ¬ M.Indist s t) :
    ∃ w : List M.Act, M.R (M.transport w s) ≠ M.R (M.transport w t) := by
  unfold Indist at h
  push_neg at h
  exact h

/-- **Maximality.** Every relation that respects responses and is a context
congruence is contained in `Indist`. That is, `Indist` is the greatest
context congruence that does not glue distinguishable responses. -/
theorem indist_greatest (r : M.St → M.St → Prop)
    (hresp : ∀ s t, r s t → M.R s = M.R t)
    (hcongr : ∀ (a : M.Act) (s t : M.St), r s t → r (M.T a s) (M.T a t))
    {s t : M.St} (h : r s t) : M.Indist s t := by
  intro w
  induction w generalizing s t with
  | nil => exact hresp s t h
  | cons a w ih =>
      simp only [transport_cons]
      exact ih (hcongr a s t h)

/-! ### The internal language as a quotient -/

/-- The equivalence relation that defines the internal language. -/
def indistSetoid (M : Machine) : Setoid M.St := ⟨M.Indist, indist_equivalence M⟩

/-- `L_S = S / ≡` — the internal language of the source. -/
def InternalLanguage (M : Machine) : Type u := Quotient (indistSetoid M)

/-- The response is well defined on the internal language: what is observed
does not depend on the choice of representative. -/
def respOnLanguage (M : Machine) : M.InternalLanguage → M.Resp :=
  Quotient.lift M.R (fun _ _ h => indist_resp h)

@[simp] theorem respOnLanguage_mk (s : M.St) :
    respOnLanguage M (Quotient.mk (indistSetoid M) s) = M.R s := rfl

/-- The contextual transport descends to the internal language — this is
the executable grammar on the quotient. -/
def actOnLanguage (M : Machine) (a : M.Act) :
    M.InternalLanguage → M.InternalLanguage :=
  Quotient.lift (fun s => Quotient.mk (indistSetoid M) (M.T a s))
    (fun _ _ h => Quotient.sound (indist_congr h a))

@[simp] theorem actOnLanguage_mk (a : M.Act) (s : M.St) :
    actOnLanguage M a (Quotient.mk (indistSetoid M) s)
      = Quotient.mk (indistSetoid M) (M.T a s) := rfl

/-! ### Approximations and stabilization -/

theorem approx_zero_iff (s t : M.St) : M.approx 0 s t ↔ M.R s = M.R t := Iff.rfl

theorem approx_succ_iff (n : ℕ) (s t : M.St) :
    M.approx (n + 1) s t ↔ M.R s = M.R t ∧ ∀ a, M.approx n (M.T a s) (M.T a t) :=
  Iff.rfl

/-- The chain of approximations is decreasing: deeper indistinguishability is stronger. -/
theorem approx_succ_le : ∀ (n : ℕ) {s t : M.St}, M.approx (n + 1) s t → M.approx n s t := by
  intro n
  induction n with
  | zero => intro s t h; exact h.1
  | succ n ih =>
      intro s t h
      exact ⟨h.1, fun a => ih (h.2 a)⟩

theorem approx_antitone {m n : ℕ} (hmn : m ≤ n) {s t : M.St}
    (h : M.approx n s t) : M.approx m s t := by
  induction n with
  | zero => have : m = 0 := Nat.le_zero.mp hmn; subst this; exact h
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact ih (Nat.lt_succ_iff.mp hlt) (approx_succ_le n h)
      · have : m = n + 1 := le_antisymm hmn hge
        subst this; exact h

/-- Indistinguishability implies indistinguishability at every finite depth. -/
theorem approx_of_indist : ∀ (n : ℕ) {s t : M.St}, M.Indist s t → M.approx n s t := by
  intro n
  induction n with
  | zero => intro s t h; exact indist_resp h
  | succ n ih =>
      intro s t h
      exact ⟨indist_resp h, fun a => ih (indist_congr h a)⟩

/-- Conversely: indistinguishability at all finite depths is indistinguishability. -/
theorem indist_of_forall_approx {s t : M.St} (h : ∀ n, M.approx n s t) :
    M.Indist s t := by
  intro w
  induction w generalizing s t with
  | nil => exact (h 0)
  | cons a w ih =>
      simp only [transport_cons]
      exact ih (fun n => (h (n + 1)).2 a)

/-- Iterative refinement converges to the direct definition. -/
theorem indist_iff_forall_approx (s t : M.St) :
    M.Indist s t ↔ ∀ n, M.approx n s t :=
  ⟨fun h n => approx_of_indist n h, indist_of_forall_approx⟩

/-! ### Stabilization on a finite source

If there are finitely many states, a decreasing chain of partitions cannot
decrease forever. So iterative refinement terminates in finitely many steps,
and the limit is reached, not merely approximated. -/

section Stabilization

variable (M : Machine) [Fintype M.St]

/-- The relation `approx n` as a set of pairs. -/
def relSet (n : ℕ) : Set (M.St × M.St) := {p | M.approx n p.1 p.2}

omit [Fintype M.St] in
theorem relSet_succ_subset (n : ℕ) : M.relSet (n + 1) ⊆ M.relSet n :=
  fun _ hp => approx_succ_le n hp

/-- The chain of partitions stabilizes in finitely many steps. -/
theorem exists_stable_index : ∃ n : ℕ, M.relSet (n + 1) = M.relSet n := by
  by_contra hcon
  push_neg at hcon
  have hstrict : ∀ n : ℕ, (M.relSet (n + 1)).ncard < (M.relSet n).ncard := by
    intro n
    exact Set.ncard_lt_ncard
      ((relSet_succ_subset M n).ssubset_of_ne (hcon n)) (Set.toFinite _)
  have hbound : ∀ n : ℕ, (M.relSet n).ncard + n ≤ (M.relSet 0).ncard := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := hstrict n; omega
  have hcontra := hbound ((M.relSet 0).ncard + 1)
  omega

variable {M}

omit [Fintype M.St] in
theorem approx_succ_iff_of_stable {n : ℕ} (h : M.relSet (n + 1) = M.relSet n)
    (s t : M.St) : M.approx (n + 1) s t ↔ M.approx n s t := by
  constructor
  · intro hst
    have hmem : (s, t) ∈ M.relSet (n + 1) := hst
    rw [h] at hmem
    exact hmem
  · intro hst
    have hmem : (s, t) ∈ M.relSet n := hst
    rw [← h] at hmem
    exact hmem

omit [Fintype M.St] in
/-- Once a fixed point is reached, refinement changes nothing further. -/
theorem approx_add_iff_of_stable {n : ℕ}
    (h : ∀ s t : M.St, M.approx (n + 1) s t ↔ M.approx n s t) :
    ∀ (m : ℕ) (s t : M.St), M.approx (n + m) s t ↔ M.approx n s t := by
  intro m
  induction m with
  | zero => intro s t; exact Iff.rfl
  | succ m ih =>
      intro s t
      have hstep : M.approx (n + (m + 1)) s t
          ↔ (M.R s = M.R t ∧ ∀ a, M.approx (n + m) (M.T a s) (M.T a t)) := by
        rw [← Nat.add_assoc]
        exact approx_succ_iff (n + m) s t
      rw [hstep]
      constructor
      · rintro ⟨hR, ha⟩
        exact (h s t).mp ⟨hR, fun a => (ih _ _).mp (ha a)⟩
      · intro hst
        obtain ⟨hR, ha⟩ := (h s t).mpr hst
        exact ⟨hR, fun a => (ih _ _).mpr (ha a)⟩

/-- **Stabilization theorem.** On a finite source there is a depth `n` at
which iterative refinement coincides with full indistinguishability by
continuations. The internal language is computed in finitely many steps. -/
theorem stabilization (M : Machine) [Fintype M.St] :
    ∃ n : ℕ, ∀ s t : M.St, M.Indist s t ↔ M.approx n s t := by
  obtain ⟨n, hn⟩ := exists_stable_index M
  refine ⟨n, fun s t => ⟨fun h => approx_of_indist n h, fun h => ?_⟩⟩
  apply indist_of_forall_approx
  intro k
  by_cases hk : k ≤ n
  · exact approx_antitone hk h
  · obtain ⟨m, rfl⟩ : ∃ m, k = n + m := ⟨k - n, by omega⟩
    exact (approx_add_iff_of_stable (approx_succ_iff_of_stable hn) m s t).mpr h

end Stabilization

end Machine

end MetaLang
