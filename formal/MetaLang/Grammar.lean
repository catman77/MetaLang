import MetaLang.Continuation

/-!
# Grammar: composition and noncommutativity

Syntax is the composition of continuation transformations. The load-bearing
content of this file is negative: **commutativity is not a law**. It may
hold in a particular world, but it has to be proved from the structure
rather than assumed for convenience; assuming it destroys the information
carried by the order of a process.

The derived quantities — probability and information — are introduced here
as well. They are defined **after** `C`, as a measure on the continuation
cone, not as primitive notions.
-/

namespace MetaLang

universe u

namespace World

variable {W : World}

/-! ### Composition of filters -/

namespace ContFilter

/-- Sequential application: first `G`, then `F`. The order of writing
matches the order of history. -/
def comp (F G : ContFilter W) : ContFilter W where
  restrict h S := F.restrict h (G.restrict h S)
  restrict_le h S := fun _ hx =>
    G.restrict_le h S (F.restrict_le h (G.restrict h S) hx)

/-- The identity filter: it narrows nothing. -/
def id (W : World) : ContFilter W where
  restrict _ S := S
  restrict_le _ _ := fun _ hx => hx

@[simp] theorem comp_id (F : ContFilter W) : F.comp (ContFilter.id W) = F := rfl

@[simp] theorem id_comp (F : ContFilter W) : (ContFilter.id W).comp F = F := rfl

theorem comp_assoc (F G H : ContFilter W) :
    (F.comp G).comp H = F.comp (G.comp H) := rfl

end ContFilter

/-! ### A world in which the order of distinctions matters -/

/-- The free world over an alphabet: every continuation is admissible.
Used as a carrier for filter countermodels. -/
abbrev freeWorld (α : Type u) : World := ⟨α, fun _ _ => True⟩

/-- A step relation that depends on the **order** of the last two events. -/
def orderStep : List Bool → Bool → Prop
  | [a, b], x => x = (a && !b)
  | _, _ => True

/-- A world in which two histories made of the same events, differing only
in order, open different continuations. -/
abbrev orderWorld : World := ⟨Bool, orderStep⟩

/-- **The order of symbols is the history.** The same events in a different
order give different continuation spaces. -/
theorem order_matters :
    orderWorld.C [true, false] ≠ orderWorld.C [false, true] := by
  intro hEq
  have h1 : true ∈ orderWorld.C [true, false] := by
    show orderStep [true, false] true
    simp [orderStep]
  rw [hEq] at h1
  have h2 : orderStep [false, true] true := h1
  simp [orderStep] at h2

/-- There exists a world whose grammar is noncommutative: the composition
of distinctions depends on order. Hence `F_a ∘ F_b = F_b ∘ F_a` is a claim
that must be proved, not an axiom of convenience. -/
theorem exists_noncommutative_world :
    ∃ (V : World.{0}) (h : List V.Sym) (x y : V.Sym),
      V.C (x :: y :: h) ≠ V.C (y :: x :: h) :=
  ⟨orderWorld, [], true, false, order_matters⟩

/-! ### Noncommutativity of filter composition -/

open scoped Classical in
/-- The filter that removes the distinction `1`. -/
noncomputable def dropOne : ContFilter (freeWorld (Fin 3)) where
  restrict _ S := S \ {1}
  restrict_le _ _ := fun _ hx => hx.1

open scoped Classical in
/-- A filter whose action depends on whether the distinction `1` is still
available: it removes `2` only in the presence of `1`. This context
dependence is exactly what breaks commutativity. -/
noncomputable def dropTwoIfOne : ContFilter (freeWorld (Fin 3)) where
  restrict _ S := if (1 : Fin 3) ∈ S then S \ {2} else S
  restrict_le _ S := by
    intro x hx
    by_cases h : (1 : Fin 3) ∈ S
    · rw [if_pos h] at hx; exact hx.1
    · rw [if_neg h] at hx; exact hx

/-- Applying `dropTwoIfOne` and then `dropOne` erases everything. -/
theorem comp_left_apply :
    (dropOne.comp dropTwoIfOne).restrict [] ({1, 2} : Set (Fin 3)) = (∅ : Set (Fin 3)) := by
  have h1 : (1 : Fin 3) ∈ ({1, 2} : Set (Fin 3)) := by simp
  show dropOne.restrict [] (dropTwoIfOne.restrict [] ({1, 2} : Set (Fin 3))) = _
  simp only [dropTwoIfOne, if_pos h1, dropOne]
  ext x
  fin_cases x <;> simp

/-- The reverse order preserves the distinction `2`. -/
theorem comp_right_apply :
    (dropTwoIfOne.comp dropOne).restrict [] ({1, 2} : Set (Fin 3)) = ({2} : Set (Fin 3)) := by
  have hstep : dropOne.restrict [] ({1, 2} : Set (Fin 3)) = ({2} : Set (Fin 3)) := by
    simp only [dropOne]
    ext x
    fin_cases x <;> simp
  show dropTwoIfOne.restrict [] (dropOne.restrict [] ({1, 2} : Set (Fin 3))) = _
  rw [hstep]
  have hno : (1 : Fin 3) ∉ ({2} : Set (Fin 3)) := by decide
  simp only [dropTwoIfOne, if_neg hno]

/-- **Filter composition is noncommutative.** The same pair of filters,
applied in different orders, gives different results. -/
theorem filter_comp_not_commutative :
    dropOne.comp dropTwoIfOne ≠ dropTwoIfOne.comp dropOne := by
  intro hEq
  have hfun := congrArg (fun F => ContFilter.restrict F [] ({1, 2} : Set (Fin 3))) hEq
  simp only at hfun
  rw [comp_left_apply, comp_right_apply] at hfun
  have h2 : (2 : Fin 3) ∈ (∅ : Set (Fin 3)) := by rw [hfun]; simp
  simp at h2

/-! ### Derived quantities: probability and information

`C` comes first. The measure `μ`, probability and information appear after
it. -/

/-- A measure on continuation cones: nonnegative and monotone. -/
structure ConeMeasure (W : World) where
  μ : Set (List W.Sym) → ℝ
  nonneg : ∀ A, 0 ≤ μ A
  mono : ∀ A B, A ⊆ B → μ A ≤ μ B

namespace ConeMeasure

variable (m : ConeMeasure W)

/-- The cone after a continuation is no larger than the original. -/
theorem measure_extend_le (h : List W.Sym) (x : W.Sym) :
    m.μ (W.Cone (x :: h)) ≤ m.μ (W.Cone h) :=
  m.mono _ _ (cone_extend_subset h x)

/-- `P(x | h) = μ(C(hx)) / μ(C(h))` — probability as a measure inside the
continuation geometry. -/
noncomputable def prob (h : List W.Sym) (x : W.Sym) : ℝ :=
  m.μ (W.Cone (x :: h)) / m.μ (W.Cone h)

/-- `I(x | h) = log (μ(C(h)) / μ(C(hx)))` — information as the reduction of
continuation uncertainty. -/
noncomputable def info (h : List W.Sym) (x : W.Sym) : ℝ :=
  Real.log (m.μ (W.Cone h) / m.μ (W.Cone (x :: h)))

theorem prob_nonneg (h : List W.Sym) (x : W.Sym) : 0 ≤ m.prob h x :=
  div_nonneg (m.nonneg _) (m.nonneg _)

/-- Probability does not exceed one — a consequence of the cone narrowing,
not a separate normalization axiom. -/
theorem prob_le_one {h : List W.Sym} (hpos : 0 < m.μ (W.Cone h)) (x : W.Sym) :
    m.prob h x ≤ 1 :=
  div_le_one_of_le₀ (m.measure_extend_le h x) (le_of_lt hpos)

/-- **Information is nonnegative.** Extending a history can only narrow the
future cone, so the logarithm of the ratio of measures is nonnegative. -/
theorem info_nonneg {h : List W.Sym} {x : W.Sym}
    (hpos : 0 < m.μ (W.Cone (x :: h))) : 0 ≤ m.info h x := by
  apply Real.log_nonneg
  rw [le_div_iff₀ hpos, one_mul]
  exact m.measure_extend_le h x

end ConeMeasure

end World

end MetaLang
