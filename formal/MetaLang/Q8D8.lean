import Mathlib

/-!
# The finite witness: `Q8` and `D8`

The core of v0.38. Two non-isomorphic sources of order 8 have isomorphic
complete diagrams of strict quotients and the same operational object `V4`.

## Encoding

The groups are given by multiplication tables over `Nat` — exactly the ones
produced by the frozen `worldmeta/base_groups.py`; the tables were
transcribed from it rather than retyped. Subsets are encoded as bitmasks,
which makes the enumeration of all 256 subsets checkable by the kernel
**without** `native_decide`.

The price of that speed is the absence of a typed group structure: the
carrier here is `Nat`. The group axioms are therefore proved explicitly
(`valid`), and isomorphism is defined by hand rather than through
`MulEquiv`.
-/

set_option maxRecDepth 10000

namespace MetaLang

/-- A finite group given by a multiplication table. -/
structure FinGroup where
  /-- Order of the group. -/
  n : Nat
  /-- Multiplication table. -/
  table : List (List Nat)
  /-- Table of inverses. -/
  invL : List Nat
  /-- The identity element. -/
  e : Nat

namespace FinGroup

variable (G : FinGroup)

/-- The carrier as a list. -/
def elems : List Nat := List.range G.n

/-- Multiplication through the table. -/
def mul (a b : Nat) : Nat := (G.table.getD a []).getD b 0

/-- Inversion through the table. -/
def inv (a : Nat) : Nat := G.invL.getD a 0

/-- The group axioms on a finite table. -/
def valid : Bool :=
  (G.e < G.n) &&
  G.elems.all (fun a => G.elems.all (fun b => G.mul a b < G.n)) &&
  G.elems.all (fun a => G.elems.all (fun b => G.elems.all (fun c =>
    G.mul (G.mul a b) c == G.mul a (G.mul b c)))) &&
  G.elems.all (fun a => (G.mul G.e a == a) && (G.mul a G.e == a)) &&
  G.elems.all (fun a => (G.mul a (G.inv a) == G.e) && (G.mul (G.inv a) a == G.e))

/-- Commutativity. -/
def isAbelian : Bool :=
  G.elems.all (fun a => G.elems.all (fun b => G.mul a b == G.mul b a))

/-- The class of non-identity elements selected by the involution test. -/
def orderClass (q : Bool) : List Nat :=
  G.elems.filter (fun a => (a != G.e) && ((G.mul a a == G.e) == q))

end FinGroup

/-! ### Tables from the frozen v0.38 code -/

/-- `Q8` in the element order `1, -1, i, -i, j, -j, k, -k`. -/
def q8 : FinGroup where
  n := 8
  table := [[0,1,2,3,4,5,6,7],[1,0,3,2,5,4,7,6],[2,3,1,0,6,7,5,4],[3,2,0,1,7,6,4,5],
            [4,5,7,6,1,0,2,3],[5,4,6,7,0,1,3,2],[6,7,4,5,3,2,1,0],[7,6,5,4,2,3,0,1]]
  invL := [0,1,3,2,5,4,7,6]
  e := 0

/-- `D8` in the element order `r^i s^j` fixed by the frozen code. -/
def d8 : FinGroup where
  n := 8
  table := [[0,1,2,3,4,5,6,7],[1,0,7,6,5,4,3,2],[2,3,4,5,6,7,0,1],[3,2,1,0,7,6,5,4],
            [4,5,6,7,0,1,2,3],[5,4,3,2,1,0,7,6],[6,7,0,1,2,3,4,5],[7,6,5,4,3,2,1,0]]
  invL := [0,1,6,3,4,5,2,7]
  e := 0

theorem q8_valid : q8.valid = true := by decide
theorem d8_valid : d8.valid = true := by decide

/-! ### The ontic difference

`Q8` has exactly one involution, `D8` has five; the counts of elements of
order 4 are 6 and 2 respectively. These are the profiles `{1:1, 2:1, 4:6}`
and `{1:1, 2:5, 4:2}` of gate `S4`. -/

theorem q8_nonabelian : q8.isAbelian = false := by decide
theorem d8_nonabelian : d8.isAbelian = false := by decide

theorem q8_involutions : (q8.orderClass true).length = 1 := by decide
theorem d8_involutions : (d8.orderClass true).length = 5 := by decide
theorem q8_order_four : (q8.orderClass false).length = 6 := by decide
theorem d8_order_four : (d8.orderClass false).length = 2 := by decide

/-! ### Isomorphism -/

/-- An isomorphism of finite groups given by a list of values. -/
structure IsIso (A B : FinGroup) (f : List Nat) : Prop where
  /-- The identity lies in the carrier. -/
  eLt : A.e < A.n
  /-- Multiplication is closed. -/
  closed : ∀ a < A.n, ∀ b < A.n, A.mul a b < A.n
  /-- Values lie in the carrier of the target. -/
  range : ∀ a < A.n, f.getD a 0 < B.n
  /-- Injectivity. -/
  inj : ∀ a < A.n, ∀ b < A.n, f.getD a 0 = f.getD b 0 → a = b
  /-- The identity maps to the identity. -/
  ident : f.getD A.e 0 = B.e
  /-- The homomorphism property. -/
  hom : ∀ a < A.n, ∀ b < A.n, f.getD (A.mul a b) 0 = B.mul (f.getD a 0) (f.getD b 0)

/-- Isomorphism of groups. -/
def Isomorphic (A B : FinGroup) : Prop := ∃ f : List Nat, IsIso A B f

/-- **Invariance of the involution class.** An isomorphism embeds the class
of non-identity elements with a given value of the test `a * a = e` into the
corresponding class of the image. It is this lemma that turns the computed
counts into a genuine invariant. -/
theorem orderClass_length_le {A B : FinGroup} {f : List Nat}
    (h : IsIso A B f) (q : Bool) :
    (A.orderClass q).length ≤ (B.orderClass q).length := by
  classical
  have hclass : ∀ (G : FinGroup) (a : Nat), a ∈ G.orderClass q ↔
      (a < G.n ∧ a ≠ G.e ∧ (G.mul a a == G.e) = q) := by
    intro G a
    constructor
    · intro ha
      have h1 := List.mem_range.mp (List.mem_of_mem_filter ha)
      have h2 := List.of_mem_filter ha
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h2
      exact ⟨h1, h2.1, h2.2⟩
    · rintro ⟨h1, h2, h3⟩
      refine List.mem_filter.mpr ⟨List.mem_range.mpr h1, ?_⟩
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      exact ⟨h2, h3⟩
  have hsub : (A.orderClass q).map (fun a => f.getD a 0) ⊆ B.orderClass q := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    obtain ⟨haLt, hane, hq⟩ := (hclass A a).mp ha
    have hgaNe : f.getD a 0 ≠ B.e := by
      intro hcon
      exact hane (h.inj a haLt A.e h.eLt (by rw [hcon, h.ident]))
    have hmulLt : A.mul a a < A.n := h.closed a haLt a haLt
    have hhom : f.getD (A.mul a a) 0 = B.mul (f.getD a 0) (f.getD a 0) :=
      h.hom a haLt a haLt
    have hpres : (B.mul (f.getD a 0) (f.getD a 0) == B.e) = (A.mul a a == A.e) := by
      by_cases hsq : A.mul a a = A.e
      · have hz : B.mul (f.getD a 0) (f.getD a 0) = B.e := by
          rw [← hhom, hsq]; exact h.ident
        rw [beq_iff_eq.mpr hz, beq_iff_eq.mpr hsq]
      · have hne : B.mul (f.getD a 0) (f.getD a 0) ≠ B.e := by
          rw [← hhom]
          intro hcon
          exact hsq (h.inj (A.mul a a) hmulLt A.e h.eLt (by rw [hcon, h.ident]))
        rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hsq]
    exact (hclass B _).mpr ⟨h.range a haLt, hgaNe, by rw [hpres, hq]⟩
  have hinjOn : ∀ a ∈ A.orderClass q, ∀ b ∈ A.orderClass q,
      f.getD a 0 = f.getD b 0 → a = b := by
    intro a ha b hb hab
    exact h.inj a ((hclass A a).mp ha).1 b ((hclass A b).mp hb).1 hab
  have hnodup : (A.orderClass q).Nodup := List.Nodup.filter _ List.nodup_range
  have hmapNodup : ((A.orderClass q).map (fun a => f.getD a 0)).Nodup :=
    hnodup.map_on hinjOn
  have hle := (List.subperm_of_subset hmapNodup hsub).length_le
  simpa using hle

/-- **`Q8` and `D8` are not isomorphic.** The witness is the difference in
the number of elements of order 4 (`S28`: the difference is exhibited
without appealing to observer labels). -/
theorem q8_not_isomorphic_d8 : ¬ Isomorphic q8 d8 := by
  rintro ⟨f, hf⟩
  have hle := orderClass_length_le hf false
  rw [q8_order_four, d8_order_four] at hle
  omega

/-- The converse direction, via the number of involutions. -/
theorem d8_not_isomorphic_q8 : ¬ Isomorphic d8 q8 := by
  rintro ⟨f, hf⟩
  have hle := orderClass_length_le hf true
  rw [d8_involutions, q8_involutions] at hle
  omega

/-! ### Strict quotients: enumerating the normal subgroups

Subsets are encoded as bitmasks, so the full sweep over all `2^8` subsets is
carried out by the kernel. A strict observer is a quotient by a normal
subgroup with a nontrivial kernel; the terminal quotient is included. -/

namespace FinGroup

/-- Membership of an element in a bitmask. -/
def maskMem (m a : Nat) : Bool := (m >>> a) % 2 == 1

/-- The elements selected by a mask. -/
def maskElems (G : FinGroup) (m : Nat) : List Nat := G.elems.filter (maskMem m)

/-- The mask defines a subgroup. -/
def isSubgroupMask (G : FinGroup) (m : Nat) : Bool :=
  maskMem m G.e &&
  (G.maskElems m).all (fun a =>
    maskMem m (G.inv a) && (G.maskElems m).all (fun b => maskMem m (G.mul a b)))

/-- The mask defines a normal subgroup. -/
def isNormalMask (G : FinGroup) (m : Nat) : Bool :=
  G.elems.all (fun g =>
    (G.maskElems m).all (fun h => maskMem m (G.mul (G.mul g h) (G.inv g))))

/-- All normal subgroups as masks. -/
def normalMasks (G : FinGroup) : List Nat :=
  (List.range (2 ^ G.n)).filter (fun m => G.isSubgroupMask m && G.isNormalMask m)

/-- Kernels of strict observers: the nontrivial normal subgroups. -/
def strictKernels (G : FinGroup) : List Nat :=
  G.normalMasks.filter (fun m => 1 < (G.maskElems m).length)

end FinGroup

/-- Strict observer kernels of `Q8`: the centre, three subgroups of order 4, the whole group. -/
def q8Kernels : List Nat := [3, 15, 51, 195, 255]

/-- Strict observer kernels of `D8` — the same lattice shape. -/
def d8Kernels : List Nat := [17, 51, 85, 153, 255]

theorem q8_strictKernels : q8.strictKernels = q8Kernels := by decide
theorem d8_strictKernels : d8.strictKernels = d8Kernels := by decide

theorem q8_objects : q8Kernels.length = 5 := by decide
theorem d8_objects : d8Kernels.length = 5 := by decide

/-! ### The operational object

`K* = ⋂ K` over all strict kernels; `S_op = G / K*`. For both groups `K*` has
order 2, and `S_op` has order 4 and exponent 2, that is, it is the Klein
four-group `V4`. -/

namespace FinGroup

/-- The mask of the coset `aK`. -/
def cosetMask (G : FinGroup) (m a : Nat) : Nat :=
  (G.maskElems m).foldl (fun acc k => acc ||| (1 <<< G.mul a k)) 0

/-- Cosets of the subgroup given by a mask. -/
def cosets (G : FinGroup) (m : Nat) : List Nat :=
  (G.elems.map (G.cosetMask m)).eraseDups

/-- A representative of the coset with index `i`. -/
def repOf (G : FinGroup) (m i : Nat) : Nat :=
  (G.maskElems ((G.cosets m).getD i 0)).headD 0

/-- The index of the coset containing `a`. -/
def quotIdx (G : FinGroup) (m a : Nat) : Nat :=
  (G.cosets m).findIdx (fun c => c == G.cosetMask m a)

/-- The quotient group by the normal subgroup given by a mask. -/
def quotient (G : FinGroup) (m : Nat) : FinGroup where
  n := (G.cosets m).length
  table := (List.range (G.cosets m).length).map (fun i =>
    (List.range (G.cosets m).length).map (fun j =>
      G.quotIdx m (G.mul (G.repOf m i) (G.repOf m j))))
  invL := (List.range (G.cosets m).length).map (fun i =>
    G.quotIdx m (G.inv (G.repOf m i)))
  e := G.quotIdx m G.e

/-- The Klein four-group: order 4 with exponent 2. These two conditions
determine `V4` uniquely among groups of order 4. -/
def isKleinFour (Q : FinGroup) : Bool :=
  Q.valid && (Q.n == 4) && Q.elems.all (fun a => Q.mul a a == Q.e)

end FinGroup

/-- The universal kernel: the intersection of all strict kernels. -/
def kstarMask (G : FinGroup) (ks : List Nat) : Nat := ks.foldl (· &&& ·) (2 ^ G.n - 1)

/-- Sizes of the diagram objects: the orders of the strict quotients. -/
def quotSizes (G : FinGroup) (ks : List Nat) : List Nat :=
  ks.map (fun m => (G.cosets m).length)

theorem q8_kstar : kstarMask q8 q8Kernels = 3 := by decide
theorem d8_kstar : kstarMask d8 d8Kernels = 17 := by decide

theorem q8_kstar_size : (q8.maskElems 3).length = 2 := by decide
theorem d8_kstar_size : (d8.maskElems 17).length = 2 := by decide

theorem q8_op_size : (q8.quotient 3).n = 4 := by decide
theorem d8_op_size : (d8.quotient 17).n = 4 := by decide

/-- **The operational object of `Q8` is `V4`.** -/
theorem q8_op_isKleinFour : (q8.quotient 3).isKleinFour = true := by decide

/-- **The operational object of `D8` is the same `V4`.** -/
theorem d8_op_isKleinFour : (d8.quotient 17).isKleinFour = true := by decide

theorem q8_quotSizes : quotSizes q8 q8Kernels = [4, 2, 2, 2, 1] := by decide
theorem d8_quotSizes : quotSizes d8 d8Kernels = [4, 2, 2, 2, 1] := by decide

/-- The object profiles of the two diagrams agree. -/
theorem q8_d8_same_object_profile : quotSizes q8 q8Kernels = quotSizes d8 d8Kernels := by
  rw [q8_quotSizes, d8_quotSizes]

end MetaLang
