import MetaLang.AlgebraicDescent
import MetaLang.RefinementOrder
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Witnesses for the meaning algebra (v0.22 §6–§7, v0.23 §8, v0.24 §7)

All the witnesses are built on **one** machine — the shift machine:

  `St = ℕ → G`,  `T x = fun i => x (i+1)`,  `R x = x 0`.

Then `approx n x y` means exactly agreement of the first `n+1` coordinates,
so the machine's filtration coincides with the prefix filtration. This
matters: "continuity" is proved about `Machine.dASC` from `ASCTopology.lean`,
not about a separately introduced look-alike metric.

Contents:

* the **nonabelian witness** (v0.22 §6, v0.23 §8): `⊕ = xy`, `⊖ = xy⁻¹`,
  `ρ = hxh⁻¹` coordinatewise; all the source laws hold, the operations are
  ASC-continuous, and `⊕` is noncommutative for `G = D₄`;
* the **nonclassical witness** (v0.22 §7): a filtration-compatible
  nonassociative magma without identity — so ASC and descent do **not**
  generate the group axioms;
* the **infinite Boolean witness** (v0.24 §7): synthesis is coordinatewise
  `or`, contrast is `x ∧ ¬y`, both operations are derived from the
  continuation order and are ASC-continuous.
-/

namespace MetaLang

namespace Witnesses

/-! ## The shift machine -/

/-- The shift machine on infinite sequences: the response is the current
coordinate and the only action is the shift. -/
abbrev shiftMachine (G : Type) : Machine.{0} where
  St := ℕ → G
  Act := Unit
  Resp := G
  T := fun _ x => fun i => x (i + 1)
  R := fun x => x 0

variable {G : Type}

theorem shift_transport (w : List Unit) (x : ℕ → G) :
    (shiftMachine G).transport w x = fun i => x (i + w.length) := by
  induction w generalizing x with
  | nil => funext i; rfl
  | cons a w ih =>
      funext i
      have := congrFun (ih (fun i => x (i + 1))) i
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- **The filtration of the shift machine is the prefix filtration.**
Agreement up to semantic depth `n` is agreement of the first `n+1`
coordinates. -/
theorem shift_approx (n : ℕ) (x y : ℕ → G) :
    (shiftMachine G).approx n x y ↔ ∀ i ≤ n, x i = y i := by
  induction n generalizing x y with
  | zero =>
      constructor
      · intro h i hi
        rw [Nat.le_zero.mp hi]
        exact h
      · intro h
        exact h 0 (Nat.le_refl 0)
  | succ n ih =>
      rw [Machine.approx_succ_iff]
      constructor
      · rintro ⟨h0, hstep⟩ i hi
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · exact h0
        · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hpos
          have := (ih _ _).mp (hstep ()) j (by omega)
          simpa [Nat.add_comm] using this
      · intro h
        refine ⟨h 0 (Nat.zero_le _), fun _ => (ih _ _).mpr ?_⟩
        intro i hi
        exact h (i + 1) (by omega)

/-- The shift machine separates everything: its semantic quotient is trivial. -/
theorem shift_indist_iff (x y : ℕ → G) :
    (shiftMachine G).Indist x y ↔ x = y := by
  constructor
  · intro h
    funext i
    have := (shift_approx i x y).mp (Machine.approx_of_indist i h)
    exact this i (Nat.le_refl i)
  · rintro rfl
    exact (shiftMachine G).indist_refl x

/-- **A witness of non-discreteness.** At every depth there is a pair of
distinct states not yet separated — which the finite chain of
`CollapseBridge` does not provide. -/
theorem shift_not_discrete {g₀ g₁ : G} (hne : g₀ ≠ g₁) (n : ℕ) :
    ∃ x y : ℕ → G, x ≠ y ∧ (shiftMachine G).approx n x y := by
  refine ⟨fun _ => g₀, fun i => if i ≤ n then g₀ else g₁, ?_, ?_⟩
  · intro h
    have := congrFun h (n + 1)
    simp only [if_neg (by omega : ¬ (n + 1 ≤ n))] at this
    exact hne this
  · exact (shift_approx n _ _).mpr fun i hi => by simp [hi]

/-- A coordinatewise binary operation preserves every level of the filtration. -/
theorem pointwise_filtrationCompat₂ (f : G → G → G) :
    (shiftMachine G).FiltrationCompat₂ (fun x y i => f (x i) (y i)) := by
  intro n x x' y y' hx hy
  refine (shift_approx n _ _).mpr fun i hi => ?_
  show f (x i) (y i) = f (x' i) (y' i)
  rw [(shift_approx n x x').mp hx i hi, (shift_approx n y y').mp hy i hi]

/-- A coordinatewise unary operation preserves every level of the filtration. -/
theorem pointwise_filtrationCompat₁ (f : G → G) :
    (shiftMachine G).FiltrationCompat₁ (fun x i => f (x i)) := by
  intro n x y hx
  refine (shift_approx n _ _).mpr fun i hi => ?_
  show f (x i) = f (y i)
  rw [(shift_approx n x y).mp hx i hi]

/-- A coordinatewise unary operation that **depends on the coordinate** also
preserves the filtration. -/
theorem pointwiseIdx_filtrationCompat₁ (f : ℕ → G → G) :
    (shiftMachine G).FiltrationCompat₁ (fun x i => f i (x i)) := by
  intro n x y hx
  refine (shift_approx n _ _).mpr fun i hi => ?_
  show f i (x i) = f i (y i)
  rw [(shift_approx n x y).mp hx i hi]

/-! ## The nonabelian group witness (v0.22 §6, v0.23 §8) -/

namespace GroupWitness

variable {G : Type} [Group G]

/-- Coordinatewise synthesis. -/
def gplus (x y : ℕ → G) : ℕ → G := fun i => x i * y i

/-- Coordinatewise contrast. -/
def gminus (x y : ℕ → G) : ℕ → G := fun i => x i * (y i)⁻¹

/-- Coordinatewise inner conjugation. -/
def grho (h : G) (x : ℕ → G) : ℕ → G := fun i => h * x i * h⁻¹

theorem gplus_assoc (x y z : ℕ → G) :
    gplus (gplus x y) z = gplus x (gplus y z) := by
  funext i; simp [gplus, mul_assoc]

/-- The identity does not depend on the operand — gate `S20` of v0.22. -/
theorem gminus_self (x : ℕ → G) : gminus x x = fun _ => 1 := by
  funext i; simp [gminus]

/-- Cancellation survives globalization — gate `S20` of v0.22. -/
theorem gminus_gplus (x y : ℕ → G) : gplus (gminus x y) y = x := by
  funext i; simp [gplus, gminus]

/-- `ρ` is an involution when `h * h = 1` — gate `S21` of v0.22. -/
theorem grho_involutive {h : G} (hh : h * h = 1) (x : ℕ → G) :
    grho h (grho h x) = x := by
  have hinv : h⁻¹ * h⁻¹ = 1 := by
    rw [← mul_inv_rev, hh, inv_one]
  funext i
  show h * (h * x i * h⁻¹) * h⁻¹ = x i
  calc h * (h * x i * h⁻¹) * h⁻¹ = (h * h) * x i * (h⁻¹ * h⁻¹) := by group
    _ = x i := by rw [hh, hinv, one_mul, mul_one]

/-- `ρ` is an automorphism — gate `S21` of v0.22. -/
theorem grho_hom (h : G) (x y : ℕ → G) :
    grho h (gplus x y) = gplus (grho h x) (grho h y) := by
  funext i
  simp only [grho, gplus]
  group

/-- All three operations are ASC-continuous — gates `S11`–`S13` of v0.22,
`S10`–`S12` v0.23. -/
theorem group_ops_continuous (h : G) :
    (shiftMachine G).FiltrationCompat₂ (gplus (G := G)) ∧
    (shiftMachine G).FiltrationCompat₂ (gminus (G := G)) ∧
    (shiftMachine G).FiltrationCompat₁ (grho (G := G) h) :=
  ⟨pointwise_filtrationCompat₂ (fun a b => a * b),
   pointwise_filtrationCompat₂ (fun a b => a * b⁻¹),
   pointwise_filtrationCompat₁ (fun a => h * a * h⁻¹)⟩

/-- Explicit 1-Lipschitz continuity of synthesis on the real scale. -/
theorem gplus_lipschitz (x x' y y' : ℕ → G) :
    (shiftMachine G).dASC (gplus x y) (gplus x' y') ≤
      max ((shiftMachine G).dASC x x') ((shiftMachine G).dASC y y') :=
  Machine.dASC_op_le_max (pointwise_filtrationCompat₂ (fun a b => a * b)) x x' y y'

open DihedralGroup in
/-- **Noncommutativity (gate `S18` of v0.22).** In `D₄ = DihedralGroup 4`
coordinatewise synthesis is noncommutative: the witness is lifted from the
group to constant sequences. -/
theorem gplus_not_comm :
    ∃ x y : ℕ → DihedralGroup 4, gplus x y ≠ gplus y x := by
  refine ⟨fun _ => r 1, fun _ => sr 0, ?_⟩
  intro h
  have := congrFun h 0
  simp only [gplus] at this
  revert this
  decide

end GroupWitness

/-! ## The nonclassical witness (v0.22 §7) -/

namespace MagmaWitness

/-- A coordinatewise magma: `x ⊕ y = x + 1`. Total, but neither associative
nor unital. -/
def mop (x y : ℕ → Fin 3) : ℕ → Fin 3 := fun i => x i + 1

theorem mop_filtrationCompat :
    (shiftMachine (Fin 3)).FiltrationCompat₂ mop :=
  pointwise_filtrationCompat₂ (fun a _ => a + 1)

/-- **Nonassociativity.** -/
theorem mop_not_assoc :
    ∃ x y z : ℕ → Fin 3, mop (mop x y) z ≠ mop x (mop y z) := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  intro h
  have := congrFun h 0
  revert this
  decide

/-- **Absence of an identity.** -/
theorem mop_no_identity :
    ¬ ∃ e : ℕ → Fin 3, ∀ x, mop e x = x ∧ mop x e = x := by
  rintro ⟨e, he⟩
  have := congrFun (he e).1 0
  simp only [mop] at this
  revert this
  generalize e 0 = a
  revert a
  decide

/-- **`ASC + descent ≠ the group axioms` (gate `S19` of v0.22, `S20` of
v0.23).** There is a filtration-compatible — hence ASC-continuous — operation
that is neither associative nor unital. -/
theorem asc_does_not_force_group_laws :
    (shiftMachine (Fin 3)).FiltrationCompat₂ mop ∧
    (∃ x y z : ℕ → Fin 3, mop (mop x y) z ≠ mop x (mop y z)) ∧
    ¬ ∃ e : ℕ → Fin 3, ∀ x, mop e x = x ∧ mop x e = x :=
  ⟨mop_filtrationCompat, mop_not_assoc, mop_no_identity⟩

end MagmaWitness

/-! ## The infinite Boolean witness (v0.24 §7) -/

namespace BooleanWitness

/-- Synthesis: coordinatewise "or". -/
def bjoin (x y : ℕ → Bool) : ℕ → Bool := fun i => x i || y i

/-- Contrast: coordinatewise `x ∧ ¬y`. -/
def bdiff (x y : ℕ → Bool) : ℕ → Bool := fun i => x i && !y i

theorem bjoin_eq_sup (x y : ℕ → Bool) : bjoin x y = x ⊔ y := by
  funext i
  cases x i <;> cases y i <;> rfl

/-- **Synthesis is derived from the order (gate `S18` of v0.24).**
Coordinatewise `or` is exactly the least upper bound in the refinement
order, not a postulate. -/
theorem bjoin_isLUB (x y : ℕ → Bool) : IsLUB {x, y} (bjoin x y) := by
  rw [bjoin_eq_sup]
  exact isLUB_pair

theorem bdiff_eq_sdiff (x y : ℕ → Bool) : bdiff x y = x \ y := by
  funext i
  cases x i <;> cases y i <;> rfl

/-- **Contrast is derived from the order (gate `S19` of v0.24).** The
relative complement is the least augmentation lifting `y` to `x ⊔ y`. -/
theorem bdiff_isLeast (x y : ℕ → Bool) :
    IsLeast {z | x ≤ y ⊔ z} (bdiff x y) := by
  constructor
  · rw [bdiff_eq_sdiff]
    simpa using le_sup_sdiff
  · intro z hz
    rw [bdiff_eq_sdiff]
    exact sdiff_le_iff.mpr hz

/-! #### The refinement order from behaviour, not from the type

v0.24 §7 specifies the continuations `a_i`: "admissible exactly when
coordinate `i` is `0`, and it turns that coordinate to `1`". Below are that
system and the theorem that its continuation language reproduces the
constraint order. -/

/-- The continuation system of the infinite Boolean witness. -/
abbrev boolSys : ContSystem where
  St := ℕ → Bool
  Act := ℕ
  step := fun i x => if x i then none else some (Function.update x i true)

theorem bool_run_mono :
    ∀ (w : List ℕ) (x y : ℕ → Bool), x ≤ y →
      (boolSys.run w y).isSome → (boolSys.run w x).isSome := by
  intro w
  induction w with
  | nil => intro x y _ _; rfl
  | cons i w ih =>
      intro x y hxy hy
      have hyi : y i = false := by
        by_contra h
        simp only [Bool.not_eq_false] at h
        simp [ContSystem.run, h] at hy
      have hxi : x i = false := by
        have hle := hxy i
        rw [hyi] at hle
        cases hx : x i with
        | false => rfl
        | true =>
            rw [hx] at hle
            exact absurd hle (by simp)
      have hupd : Function.update x i true ≤ Function.update y i true := by
        intro j
        by_cases hj : j = i
        · subst hj; simp
        · simpa [Function.update_of_ne hj] using hxy j
      simp only [ContSystem.run, hxi, hyi, Bool.false_eq_true, if_false,
        Option.bind] at hy ⊢
      exact ih _ _ hupd hy

/-- **The constraint order is recovered from the continuation language
(gates `S1`, `S2`, `S18` of v0.24).** -/
theorem bool_refines_iff_le (x y : ℕ → Bool) : boolSys.refines x y ↔ x ≤ y := by
  constructor
  · intro h i
    cases hy : y i with
    | true => simp [hy]
    | false =>
        have hmem : [i] ∈ boolSys.Paths y := by
          show (boolSys.run [i] y).isSome = true
          simp [ContSystem.run, hy]
        have hx : (boolSys.run [i] x).isSome = true := h hmem
        cases hxi : x i with
        | false => simp [hxi, hy]
        | true => simp [ContSystem.run, hxi] at hx
  · intro hxy w hw
    exact bool_run_mono w x y hxy hw

/-- **Both derived operations are ASC-continuous (gate `S20` of v0.24).** -/
theorem boolean_ops_continuous :
    (shiftMachine Bool).FiltrationCompat₂ bjoin ∧
    (shiftMachine Bool).FiltrationCompat₂ bdiff :=
  ⟨pointwise_filtrationCompat₂ (fun a b => a || b),
   pointwise_filtrationCompat₂ (fun a b => a && !b)⟩

/-- The infinite witness is non-discrete: at every depth distinct points
remain unseparated. -/
theorem boolean_not_discrete (n : ℕ) :
    ∃ x y : ℕ → Bool, x ≠ y ∧ (shiftMachine Bool).approx n x y :=
  shift_not_discrete (by decide : (false : Bool) ≠ true) n

end BooleanWitness

/-! ## Reflection on an infinite Boolean carrier (gate `S17` of v0.25)

`Reflection.lean` proves the reflection theorem abstractly, but its
witnesses are finite (`Fin 4`). Here is an infinite one: the subspace is
given by a set of coordinates required to be active. -/

namespace InfiniteReflection

variable (A : ℕ → Bool)

/-- The target subspace: the coordinates in `A` are active. -/
def Target : Set (ℕ → Bool) := {x | ∀ i, A i = true → x i = true}

/-- The reflector: switch on the required coordinates and leave the rest alone. -/
def refl (x : ℕ → Bool) : ℕ → Bool := fun i => A i || x i

variable {A}

theorem refl_mem (x : ℕ → Bool) : refl A x ∈ Target A := by
  intro i hi
  simp [refl, hi]

/-- Inflationarity. -/
theorem refl_inflationary (x : ℕ → Bool) : x ≤ refl A x := by
  intro i
  cases hx : x i <;> simp [refl, hx]

/-- Monotonicity. -/
theorem refl_monotone {x y : ℕ → Bool} (h : x ≤ y) : refl A x ≤ refl A y := by
  intro i
  have hi := h i
  cases hA : A i <;> cases hx : x i <;> cases hy : y i <;>
    simp_all [refl]

/-- **Idempotence on an infinite carrier (gate `S17` of v0.25).** -/
theorem refl_idempotent (x : ℕ → Bool) : refl A (refl A x) = refl A x := by
  funext i
  cases hA : A i <;> simp [refl, hA]

/-- The fixed points of the reflector are exactly the target subspace. -/
theorem fix_eq_target (x : ℕ → Bool) : refl A x = x ↔ x ∈ Target A := by
  constructor
  · intro h i hi
    have := congrFun h i
    simp [refl, hi] at this
    exact this
  · intro h
    funext i
    cases hA : A i with
    | false => simp [refl, hA]
    | true => simp [refl, hA, h i hA]

end InfiniteReflection

end Witnesses

end MetaLang
