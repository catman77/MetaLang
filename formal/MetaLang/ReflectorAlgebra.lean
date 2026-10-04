import MetaLang.Reflection

/-!
# The algebra of reflectors (v0.26)

What happens when several independently justified semantic conditions are
imposed at once? The corpus's key distinction:

* the **operational composition** of reflectors is ordered and may fail to
  commute;
* the **joint enforcement** of their fixed spaces is a closure construction.

Global commutativity is **not** assumed. Three things are proved: the common
fixed space of both compositions equals `F ∩ G`; a raw composition may fail
to be idempotent, i.e. reflectors are **not closed** under composition; and
on a finite order, saturating either composition leads to the same reflection
into `F ∩ G` — independently of the order.
-/

namespace MetaLang

universe u

section FixedSpace

variable {α : Type u} [PartialOrder α]

/-- **The fixed space of a composition.** Both compositions have the same
fixed space — the intersection. The proof from v0.26 §3: from `c (d x) = x`,
inflationarity gives `x ≤ d x ≤ c (d x) = x`. -/
theorem fix_comp_iff (c d : ClosureOperator α) (x : α) :
    c (d x) = x ↔ (c x = x ∧ d x = x) := by
  constructor
  · intro hx
    have h1 : x ≤ d x := d.le_closure' x
    have h2 : d x ≤ c (d x) := c.le_closure' (d x)
    rw [hx] at h2
    have hdx : d x = x := le_antisymm h2 h1
    refine ⟨?_, hdx⟩
    calc c x = c (d x) := by rw [hdx]
      _ = x := hx
  · rintro ⟨hc, hd⟩
    rw [hd, hc]

/-- Both orders of composition give the same fixed space. -/
theorem fix_comp_symm (c d : ClosureOperator α) (x : α) :
    c (d x) = x ↔ d (c x) = x := by
  rw [fix_comp_iff, fix_comp_iff, and_comm]

/-- **The conjunction of conditions is the fixed space of the composition**
(`S8`). The logical conjunction of reflective conditions is exactly the
intersection of their fixed spaces, that is, the fixed space of the
composition of reflectors, in either order. -/
theorem conj_eq_fix_comp (c d : ClosureOperator α) :
    {x : α | c (d x) = x} = {x : α | c x = x} ∩ {x : α | d x = x} := by
  ext x
  exact fix_comp_iff c d x

/-- If the reflectors commute, the composition is itself a reflector. -/
theorem comp_idempotent_of_commute (c d : ClosureOperator α)
    (hcomm : ∀ x, c (d x) = d (c x)) (x : α) :
    c (d (c (d x))) = c (d x) := by
  have h1 : c (d x) = d (c x) := hcomm x
  calc c (d (c (d x))) = c (d (d (c x))) := by rw [h1]
    _ = c (d (c x)) := by rw [d.idempotent]
    _ = c (c (d x)) := by rw [← h1]
    _ = c (d x) := c.idempotent _

end FixedSpace

/-! ### Saturation on a finite order -/

section Saturation

variable {α : Type u} [PartialOrder α]

/-- Iteration of an operator. -/
def iter (g : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => g (iter g n x)

theorem le_iter (g : α → α) (hg : ∀ x, x ≤ g x) (x : α) :
    ∀ n, iter g n x ≤ iter g (n + 1) x := by
  intro n
  exact hg _

theorem iter_mono_nat (g : α → α) (hg : ∀ x, x ≤ g x) (x : α) :
    Monotone (fun n => iter g n x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_iter g hg x n

/-- **Saturation.** On a finite order the iteration of an inflationary
operator stabilizes. -/
theorem exists_stable_iter [Finite α] (g : α → α) (hg : ∀ x, x ≤ g x) (x : α) :
    ∃ n, g (iter g n x) = iter g n x := by
  by_contra hcon
  push_neg at hcon
  have hstrict : StrictMono (fun n => iter g n x) := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact lt_of_le_of_ne (le_iter g hg x n) (fun h => hcon n h.symm)
  obtain ⟨p, q, hpq, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n => iter g n x)
  exact hpq (hstrict.injective heq)

/-- Saturation does not overshoot a common fixed point: if `z` is fixed for
both reflectors and lies above `x`, the iteration never passes it. -/
theorem iter_le_of_fixed (c d : ClosureOperator α) {x z : α}
    (hz : c z = z ∧ d z = z) (hxz : x ≤ z) :
    ∀ n, iter (fun y => c (d y)) n x ≤ z := by
  intro n
  induction n with
  | zero => exact hxz
  | succ n ih =>
      show c (d (iter (fun y => c (d y)) n x)) ≤ z
      calc c (d (iter (fun y => c (d y)) n x))
          ≤ c (d z) := c.monotone' (d.monotone' ih)
        _ = z := by rw [hz.2, hz.1]

end Saturation

/-! ### A concrete noncommuting pair

The chain `0 < 1 < 2 < 3` and two reflectors: into `{1,3}` and into `{2,3}`.
One composition reaches the joint reflector in a single pass, the other does
not — and is **not idempotent**. This is the `directed_chain` family of
v0.26. -/

/-- The reflector into `{1, 3}`. -/
def cFun : Fin 4 → Fin 4 := fun x => if x ≤ 1 then 1 else 3

/-- The reflector into `{2, 3}`. -/
def dFun : Fin 4 → Fin 4 := fun x => if x ≤ 2 then 2 else 3

/-- The first reflector as a closure operator. -/
def cOp : ClosureOperator (Fin 4) where
  toFun := cFun
  monotone' := by decide
  le_closure' := by decide
  idempotent' := by decide

/-- The second reflector as a closure operator. -/
def dOp : ClosureOperator (Fin 4) where
  toFun := dFun
  monotone' := by decide
  le_closure' := by decide
  idempotent' := by decide

/-- **Reflectors are not closed under composition.** The composition
`d ∘ c` is inflationary and monotone but **not idempotent**. -/
theorem comp_not_idempotent :
    ∃ x : Fin 4, dOp (cOp (dOp (cOp x))) ≠ dOp (cOp x) :=
  ⟨0, by decide⟩

/-- The reverse order reaches the joint reflector in a single pass. -/
theorem other_comp_idempotent :
    ∀ x : Fin 4, cOp (dOp (cOp (dOp x))) = cOp (dOp x) := by decide

/-- The pair genuinely fails to commute. -/
theorem ops_not_commute : ∃ x : Fin 4, cOp (dOp x) ≠ dOp (cOp x) :=
  ⟨0, by decide⟩

/-- The common fixed space of both compositions is the single point `{3}`. -/
theorem joint_fixed_space :
    ∀ x : Fin 4, (cOp (dOp x) = x ↔ x = 3) := by decide

/-- **Saturation is order-independent.** Both compositions, once iterated,
arrive at the same point — the joint reflector. -/
theorem saturation_order_independent :
    ∀ x : Fin 4, iter (fun y => cOp (dOp y)) 2 x = iter (fun y => dOp (cOp y)) 2 x := by
  decide

end MetaLang
