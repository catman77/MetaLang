import Mathlib

/-!
# The logic of admissible semantic constraints (v0.27, v0.28)

The SRT idea "an axiom is a filter of admissible continuations" turns into
an internal logic: conditions are **reflective subspaces**, that is Moore
families; entailment is inclusion; conjunction is intersection; disjunction
is the Moore hull of the union.

The carrier here is `B3` — the Boolean lattice on three atoms (8 points) —
with meet given by bitwise AND and top equal to 7. Subsets are encoded as
masks, as in `Q8D8`, so the whole enumeration is checked by the kernel
without `native_decide`.

The main result and the main surprise of the corpus (`S11`, `S12`):
**a Boolean semantic carrier generates a non-distributive logic of
conditions.**
-/

set_option maxRecDepth 10000

namespace MetaLang

namespace B3

/-- Membership of a point in a mask. -/
def mem (m a : Nat) : Bool := (m >>> a) % 2 == 1

/-- The points of the carrier. -/
def points : List Nat := List.range 8

/-- The top of the Boolean carrier. -/
def top : Nat := 7

/-- The mask defines a Moore family: it contains the top and is meet-closed. -/
def isMoore (m : Nat) : Bool :=
  mem m top &&
  points.all (fun a => !mem m a ||
    points.all (fun b => !mem m b || mem m (a &&& b)))

/-- All conditions: the reflective subspaces of `B3`. -/
def conditions : List Nat := (List.range 256).filter isMoore

/-- **There are exactly 61 conditions** — the full envelope from `FROZEN_PROTOCOL.md` of v0.27. -/
theorem conditions_count : conditions.length = 61 := by decide

/-! ### The operations of the logic -/

/-- One step of meet closure. -/
def hullStep (m : Nat) : Nat :=
  points.foldl (fun acc a =>
    points.foldl (fun acc2 b =>
      if mem m a && mem m b then acc2 ||| (1 <<< (a &&& b)) else acc2) acc) m

/-- The Moore hull: add the top and close under meet. -/
def hull (m : Nat) : Nat :=
  Nat.rec (m ||| (1 <<< top)) (fun _ acc => hullStep acc) 4

/-- Entailment of conditions is inclusion. -/
def entails (a b : Nat) : Bool := (a &&& b) == a

/-- Conjunction is intersection. -/
def conj (a b : Nat) : Nat := a &&& b

/-- Disjunction is the Moore hull of the union. -/
def disj (a b : Nat) : Nat := hull (a ||| b)

/-- The strongest condition: the top alone. -/
def bot : Nat := 1 <<< top

/-- The weakest condition: the whole carrier. -/
def topCond : Nat := 255

theorem bot_isMoore : isMoore bot = true := by decide
theorem topCond_isMoore : isMoore topCond = true := by decide

/-- Conjunction does not leave the class of conditions. -/
theorem conj_closed :
    conditions.all (fun a => conditions.all (fun b => isMoore (conj a b))) = true := by
  decide

set_option maxHeartbeats 4000000 in
/-- The hull of any mask is always a condition. The check is per element
(256 masks) rather than per pair: an enumeration with `hull` over pairs is
beyond the kernel. -/
theorem hull_isMoore : (List.range 256).all (fun m => isMoore (hull m)) = true := by
  decide

set_option maxHeartbeats 4000000 in
/-- The hull only adds points. -/
theorem le_hull : (List.range 256).all (fun m => entails m (hull m)) = true := by
  decide

/-! The following facts are proved structurally rather than by enumeration. -/

/-- Entailment is transitive. -/
theorem entails_trans {x y z : Nat} (hxy : entails x y = true) (hyz : entails y z = true) :
    entails x z = true := by
  simp only [entails, beq_iff_eq] at *
  calc x &&& z = (x &&& y) &&& z := by rw [hxy]
    _ = x &&& (y &&& z) := by rw [Nat.and_assoc]
    _ = x &&& y := by rw [hyz]
    _ = x := hxy

/-- An operand entails the union. -/
theorem entails_or_left (a b : Nat) : entails a (a ||| b) = true := by
  simp only [entails, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_and, Nat.testBit_or]
  tauto

theorem entails_or_right (a b : Nat) : entails b (a ||| b) = true := by
  simp only [entails, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_and, Nat.testBit_or]
  tauto

/-- Extracting a per-element fact from a bounded enumeration. -/
theorem of_range256 {P : Nat → Bool} (h : (List.range 256).all P = true)
    {m : Nat} (hm : m < 256) : P m = true := by
  rw [List.all_eq_true] at h
  exact h m (List.mem_range.mpr hm)

/-- **Disjunction is an upper bound in the entailment order.** -/
theorem disj_is_upper_bound {a b : Nat} (hab : (a ||| b) < 256) :
    entails a (disj a b) = true ∧ entails b (disj a b) = true :=
  ⟨entails_trans (entails_or_left a b) (of_range256 le_hull hab),
   entails_trans (entails_or_right a b) (of_range256 le_hull hab)⟩

/-- Disjunction does not leave the class of conditions. -/
theorem disj_isMoore {a b : Nat} (hab : (a ||| b) < 256) : isMoore (disj a b) = true :=
  of_range256 hull_isMoore hab

/-- Boundedness: every condition lies between the strongest and the weakest. -/
theorem bounded :
    conditions.all (fun a => entails bot a && entails a topCond) = true := by
  decide

/-! ### Non-distributivity

Three conditions: `a = {0,7}`, `b = {1,7}`, `c = {2,7}`. The disjunction of
`b` and `c` is forced to contain `1 ⊓ 2 = 0`, so the intersection with `a`
keeps `0`, whereas the pointwise distribution loses it. -/

theorem witness_a_isMoore : isMoore 129 = true := by decide
theorem witness_b_isMoore : isMoore 130 = true := by decide
theorem witness_c_isMoore : isMoore 132 = true := by decide

/-- **A Boolean carrier generates a non-distributive logic of conditions**
(`S11`). This is the main negative result of v0.27: distributivity of the
semantic carrier is **not** inherited by the logic of its reflective
subspaces. -/
theorem not_distributive :
    conj 129 (disj 130 132) ≠ disj (conj 129 130) (conj 129 132) := by decide

/-- The witness spelled out: on the left the point `0` survives, on the right it does not. -/
theorem not_distributive_explicit :
    conj 129 (disj 130 132) = 129 ∧ disj (conj 129 130) (conj 129 132) = 128 := by
  decide

/-! ### Implication is an antichain

The generalized implication is the set of **maximal** `X` with `a ⊓ X ⊨ b`.
It is not always point-valued (Heyting). -/

/-- The implication candidates. -/
def impCandidates (a b : Nat) : List Nat :=
  conditions.filter (fun x => entails (conj a x) b)

/-- The implication antichain: the maximal candidates. -/
def impAntichain (a b : Nat) : List Nat :=
  (impCandidates a b).filter (fun x =>
    (impCandidates a b).all (fun y => !(entails x y) || x == y))

/-- **Implication is multivalued.** For `a = {0,7}` and the strongest
condition `b` there are three maximal solutions: the logic of conditions is
not Heyting. -/
theorem implication_multivalued : impAntichain 129 128 = [170, 204, 240] := by decide

theorem implication_not_singleton : (impAntichain 129 128).length = 3 := by decide

/-- **Residuation when implication is point-valued.** Where the implication
antichain is a singleton, it behaves as a genuine residual:
`X ⊨ I ⟺ a ⊓ X ⊨ b`. Witness: `a = 136`, `b = 128`, with the unique maximal
solution `I = 247`. -/
theorem implication_singleton_witness : impAntichain 136 128 = [247] := by decide

theorem singleton_implication_residuates :
    conditions.all (fun x => entails x 247 == entails (conj 136 x) 128) = true := by
  decide

/-- Negation is implication into the strongest condition; it too is multivalued. -/
def neg (a : Nat) : List Nat := impAntichain a bot

theorem negation_multivalued : (neg 129).length = 3 := by decide

end B3

/-! ### The v0.28 countermodel: public indistinguishability

For every valid semantic filter there is an invalid mimic with the **same
public extension**, differing only on the hidden copy. Public extensional
behaviour therefore cannot classify source admissibility: what is needed is
a source-first criterion, not a utility. -/

namespace Nuisance

/-- A state: the public part and the hidden copy. -/
abbrev St := Bool × Bool

/-- A filter respects the factorization when it does not see the hidden copy. -/
def Descends (f : St → Bool) : Prop := ∀ a b b', f (a, b) = f (a, b')

instance (f : St → Bool) : Decidable (Descends f) := by
  unfold Descends
  infer_instance

/-- A valid filter: it depends only on the public part. -/
def valid : St → Bool := fun p => p.1

/-- The mimic: indistinguishable on the public slice, yet it reads the hidden copy. -/
def mimic : St → Bool := fun p => p.1 && p.2

theorem valid_descends : Descends valid := by decide

theorem mimic_not_descends : ¬ Descends mimic := by decide

/-- On the public slice the two agree at every point. -/
theorem same_public_extension : ∀ a : Bool, valid (a, true) = mimic (a, true) := by decide

/-- **Public behaviour does not classify source admissibility.** Two filters
are publicly indistinguishable, yet one respects the factorization and the
other does not. So the admissibility criterion cannot be extensional. -/
theorem public_behaviour_does_not_classify :
    ∃ f g : St → Bool,
      (∀ a : Bool, f (a, true) = g (a, true)) ∧ Descends f ∧ ¬ Descends g :=
  ⟨valid, mimic, same_public_extension, valid_descends, mimic_not_descends⟩

end Nuisance

end MetaLang
