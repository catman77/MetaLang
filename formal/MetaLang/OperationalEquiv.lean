import MetaLang.Q8D8

/-!
# Operational equivalence

The diagram of strict quotients as finite data: a list of object sizes and a
matrix of arrows. An isomorphism of diagrams is a bijection of objects
preserving both the sizes and the **arrows**.

Two sharpness claims, matching gates `S22`, `S23`, `S29`:

* the equivalence is **weaker** than ontic isomorphism — witness `Q8`/`D8`;
* the equivalence is **stronger** than agreement of the object profile —
  witness `scrambledDiagram`, whose profile is the same but whose arrows
  differ.
-/

set_option maxRecDepth 10000

namespace MetaLang

/-- A finite observation diagram. -/
structure FinDiagram where
  /-- Orders of the quotient objects. -/
  sizes : List Nat
  /-- Arrow matrix: `arrows[i][j]` says whether there is an arrow `i → j`. -/
  arrows : List (List Bool)

namespace FinDiagram

/-- The number of objects. -/
def nObj (D : FinDiagram) : Nat := D.sizes.length

/-- Presence of an arrow. -/
def arrow (D : FinDiagram) (i j : Nat) : Bool := (D.arrows.getD i []).getD j false

/-- The total number of arrows, identities included. -/
def arrowCount (D : FinDiagram) : Nat :=
  ((List.range D.nObj).map (fun i =>
    ((List.range D.nObj).filter (fun j => D.arrow i j)).length)).sum

end FinDiagram

/-- The strict-quotient diagram of a group: objects are quotients by strict
kernels, arrows are the maps induced by inclusion of kernels. -/
def strictDiagram (G : FinGroup) (ks : List Nat) : FinDiagram where
  sizes := quotSizes G ks
  arrows := (List.range ks.length).map (fun i =>
    (List.range ks.length).map (fun j =>
      ((ks.getD i 0) &&& (ks.getD j 0)) == ks.getD i 0))

/-- The complete strict-quotient diagram of `Q8`. -/
def q8Diagram : FinDiagram := strictDiagram q8 q8Kernels

/-- The complete strict-quotient diagram of `D8`. -/
def d8Diagram : FinDiagram := strictDiagram d8 d8Kernels

theorem q8_diagram_objects : q8Diagram.nObj = 5 := by decide
theorem d8_diagram_objects : d8Diagram.nObj = 5 := by decide
theorem q8_diagram_arrows : q8Diagram.arrowCount = 12 := by decide
theorem d8_diagram_arrows : d8Diagram.arrowCount = 12 := by decide

/-- An isomorphism of diagrams: a bijection of objects preserving sizes and arrows. -/
def isDiagramIso (A B : FinDiagram) (p : List Nat) : Bool :=
  (p.length == A.nObj) && (A.nObj == B.nObj) &&
  (List.range A.nObj).all (fun i =>
    (A.sizes.getD i 0 == B.sizes.getD (p.getD i 0) 0) &&
    (List.range A.nObj).all (fun j =>
      A.arrow i j == B.arrow (p.getD i 0) (p.getD j 0)))

/-- Insertion of an element at every position. A hand-written structurally
recursive implementation: `List.permutations` does not reduce in the
kernel. -/
def insertEverywhere (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertEverywhere x ys).map (fun l => y :: l)

/-- All permutations of a list. -/
def permsOf : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (permsOf xs).flatMap (insertEverywhere x)

/-- All isomorphisms between two diagrams. -/
def diagramIsos (A B : FinDiagram) : List (List Nat) :=
  (permsOf (List.range A.nObj)).filter (isDiagramIso A B)

/-- **The diagrams of `Q8` and `D8` are isomorphic, with exactly six
witnesses** — this is `S₃` permuting the three kernels of order 4. The count
matches `n_natural_iso_witnesses = 6` in the frozen `verdict.json` of
v0.38. -/
theorem q8_d8_diagram_iso_count : (diagramIsos q8Diagram d8Diagram).length = 6 := by decide

theorem q8_d8_diagram_equivalent : diagramIsos q8Diagram d8Diagram ≠ [] := by decide

/-- **Operational equivalence is symmetric on the positive witness (gate
`S39` of v0.38).** A diagram isomorphism exists in both directions. -/
theorem d8_q8_diagram_equivalent : diagramIsos d8Diagram q8Diagram ≠ [] := by decide

/-! ### The scramble countermodel

The object profile is preserved and a single arrow is altered. A check by
object sizes would let such a diagram through; a check by arrows rejects
it. -/

/-- Flip one entry of a row. -/
def flipRow (row : List Bool) (j : Nat) : List Bool :=
  (List.range row.length).map (fun c =>
    if c == j then !(row.getD c false) else row.getD c false)

/-- Flip one arrow of the matrix. -/
def flipAt (rows : List (List Bool)) (i j : Nat) : List (List Bool) :=
  (List.range rows.length).map (fun r =>
    if r == i then flipRow (rows.getD r []) j else rows.getD r [])

/-- A diagram with the same object profile but an altered arrow. -/
def scrambledDiagram : FinDiagram where
  sizes := d8Diagram.sizes
  arrows := flipAt d8Diagram.arrows 1 2

/-- The scramble has the very same object profile (`S22`). -/
theorem scramble_same_profile : scrambledDiagram.sizes = q8Diagram.sizes := by decide

/-- Yet there is no diagram isomorphism (`S23`): the arrow structure carries
information beyond the object profile. -/
theorem scramble_rejected : diagramIsos q8Diagram scrambledDiagram = [] := by decide

/-! ### The closing claims of v0.38 -/

/-- **Operational equivalence of `Q8` and `D8`.**

The sources are non-isomorphic; their complete strict-quotient diagrams are
isomorphic; the operational object of each is the Klein four-group `V4`. -/
theorem q8_d8_operationally_equivalent :
    ¬ Isomorphic q8 d8 ∧
      ¬ Isomorphic d8 q8 ∧
      diagramIsos q8Diagram d8Diagram ≠ [] ∧
      (q8.quotient 3).isKleinFour = true ∧
      (d8.quotient 17).isKleinFour = true :=
  ⟨q8_not_isomorphic_d8, d8_not_isomorphic_q8, q8_d8_diagram_equivalent,
   q8_op_isKleinFour, d8_op_isKleinFour⟩

/-- **Operational equivalence is strictly weaker than ontic isomorphism.**
There exist operationally equivalent but non-isomorphic sources. -/
theorem operational_equivalence_weaker_than_isomorphism :
    ∃ A B : FinGroup, ∃ ksA ksB : List Nat,
      ¬ Isomorphic A B ∧ diagramIsos (strictDiagram A ksA) (strictDiagram B ksB) ≠ [] :=
  ⟨q8, d8, q8Kernels, d8Kernels, q8_not_isomorphic_d8, q8_d8_diagram_equivalent⟩

/-- **Operational equivalence is strictly stronger than agreement of the
object profile.** There exist diagrams with the same profile and no
isomorphism. -/
theorem operational_equivalence_stronger_than_object_profile :
    ∃ A B : FinDiagram, A.sizes = B.sizes ∧ diagramIsos A B = [] :=
  ⟨q8Diagram, scrambledDiagram, scramble_same_profile.symm, scramble_rejected⟩

/-- **Ontological underdetermination.**

Complete science relative to the declared observation class determines the
operational object and the observation diagram, but it does not single out a
unique ontic representative: `Q8` and `D8` give the same observable
structure while remaining different sources. -/
theorem ontological_underdetermination :
    ∃ A B : FinGroup,
      (¬ Isomorphic A B) ∧
      (A.quotient (kstarMask A q8Kernels)).isKleinFour = true ∧
      (B.quotient (kstarMask B d8Kernels)).isKleinFour = true ∧
      diagramIsos (strictDiagram A q8Kernels) (strictDiagram B d8Kernels) ≠ [] := by
  refine ⟨q8, d8, q8_not_isomorphic_d8, ?_, ?_, q8_d8_diagram_equivalent⟩
  · rw [q8_kstar]; exact q8_op_isKleinFour
  · rw [d8_kstar]; exact d8_op_isKleinFour

end MetaLang
