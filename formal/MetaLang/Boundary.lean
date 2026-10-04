import MetaLang.InternalLanguage
import Mathlib

/-!
# Boundaries: two negative results

The two results of the corpus that no interpretation is allowed to
forget:

  `semantic structure ⇏ utility`
  `correspondence ⇏ causal channel`

The first: structural invariance does not mean positive value. A market can
have a language and still yield no profit (v0.3: market sign AUC 0.4986,
`p = 0.872`). The second: a stable correspondence between two systems is not
yet transmission of information; a channel requires an intervention that
changes what the receiver observes (v0.3–v0.4: address AUC 0.80 with
hidden-content AUC 0.52).

Both are formalized as countermodels: a witness is exhibited, not a
caveat.
-/

namespace MetaLang

/-! ### `semantic structure ⇏ utility` -/

namespace Machine

/-- A utility computed from the semantics itself: the response after a fixed
word of contexts. Such a utility respects the internal language by
construction. -/
def utilityOf (M : Machine) (w : List M.Act) (f : M.Resp → ℝ) : M.St → ℝ :=
  fun s => f (M.R (M.transport w s))

theorem utilityOf_respects_indist (M : Machine) (w : List M.Act) (f : M.Resp → ℝ)
    {s t : M.St} (h : M.Indist s t) : M.utilityOf w f s = M.utilityOf w f t := by
  unfold utilityOf
  rw [h w]

end Machine

/-- A utility that values reaching the observable state. -/
noncomputable def uPos : latentMachine.St → ℝ :=
  latentMachine.utilityOf [(), ()] (fun b => if b then 1 else 0)

/-- A utility that values exactly the opposite. -/
noncomputable def uNeg : latentMachine.St → ℝ :=
  latentMachine.utilityOf [(), ()] (fun b => if b then 0 else 1)

theorem uPos_zero : uPos 0 = 1 := by
  have h : latentR (latentMachine.transport [(), ()] 0) = true := by decide
  simp [uPos, Machine.utilityOf, h]

theorem uPos_one : uPos 1 = 0 := by
  have h : latentR (latentMachine.transport [(), ()] 1) = false := by decide
  simp [uPos, Machine.utilityOf, h]

theorem uNeg_zero : uNeg 0 = 0 := by
  have h : latentR (latentMachine.transport [(), ()] 0) = true := by decide
  simp [uNeg, Machine.utilityOf, h]

theorem uNeg_one : uNeg 1 = 1 := by
  have h : latentR (latentMachine.transport [(), ()] 1) = false := by decide
  simp [uNeg, Machine.utilityOf, h]

/-- **`semantic structure ⇏ utility`.** One and the same semantic structure
is compatible with two utilities that induce **opposite** preferences. Both
are computed from the structure itself and both respect the internal
language — so the structure does not determine value. -/
theorem structure_does_not_imply_utility :
    ∃ (M : Machine.{0}) (U₁ U₂ : M.St → ℝ) (a b : M.St),
      (∀ s t : M.St, M.Indist s t → U₁ s = U₁ t) ∧
      (∀ s t : M.St, M.Indist s t → U₂ s = U₂ t) ∧
      U₁ b < U₁ a ∧ U₂ a < U₂ b := by
  refine ⟨latentMachine, uPos, uNeg, 0, 1, ?_, ?_, ?_, ?_⟩
  · intro s t h
    exact Machine.utilityOf_respects_indist _ _ _ h
  · intro s t h
    exact Machine.utilityOf_respects_indist _ _ _ h
  · rw [uPos_zero, uPos_one]; norm_num
  · rw [uNeg_zero, uNeg_one]; norm_num

/-! ### `correspondence ⇏ causal channel` -/

/-- Two parties with a hidden common cause. The receiver's readings **may in
general** depend on an intervention on the sender's side — so the presence of
a channel is a substantive question here, not a consequence of the
definition. -/
structure TwoParty where
  /-- The hidden cause. -/
  H : Type
  /-- Interventions on the sender's side. -/
  Act : Type
  /-- The sender's readings. -/
  XS : Type
  /-- The receiver's readings. -/
  XR : Type
  /-- The sender's observation. -/
  send : H → Act → XS
  /-- The receiver's observation. -/
  recv : H → Act → XR

namespace TwoParty

/-- **Correspondence**: the two parties' readings agree — the sender's
reading is recoverable from the receiver's. -/
def Correspondence (C : TwoParty) : Prop :=
  ∀ (h₁ h₂ : C.H) (a : C.Act), C.recv h₁ a = C.recv h₂ a → C.send h₁ a = C.send h₂ a

/-- **Channel**: an intervention on the sender's side changes what the
receiver observes. This is `do(I₁) ≠ do(I₂)` on the receiver's side. -/
def HasChannel (C : TwoParty) : Prop :=
  ∃ (h : C.H) (a₁ a₂ : C.Act), C.recv h a₁ ≠ C.recv h a₂

end TwoParty

/-- The common-cause setup: both parties read the same hidden state, and an
intervention changes nothing. -/
abbrev commonCause : TwoParty where
  H := Bool
  Act := Bool
  XS := Bool
  XR := Bool
  send := fun h _ => h
  recv := fun h _ => h

/-- A setup with a genuine channel — this shows that `HasChannel` is
satisfiable and the definition is not degenerate. -/
abbrev realChannel : TwoParty where
  H := Unit
  Act := Bool
  XS := Bool
  XR := Bool
  send := fun _ a => a
  recv := fun _ a => a

theorem realChannel_hasChannel : realChannel.HasChannel :=
  ⟨(), true, false, by decide⟩

theorem commonCause_correspondence : commonCause.Correspondence := by
  intro h₁ h₂ a hrecv
  exact hrecv

theorem commonCause_no_channel : ¬ commonCause.HasChannel := by
  rintro ⟨h, a₁, a₂, hne⟩
  exact hne rfl

/-- **`correspondence ⇏ causal channel`.** There is a setup with perfect
correspondence of both parties' readings in which no intervention by the
sender changes what the receiver observes. The correspondence is there; the
channel is not. -/
theorem correspondence_does_not_imply_channel :
    ∃ C : TwoParty, C.Correspondence ∧ ¬ C.HasChannel :=
  ⟨commonCause, commonCause_correspondence, commonCause_no_channel⟩

/-- Both negative results together: structure does not imply value, and
correspondence does not imply a channel. -/
theorem boundary_results :
    (∃ (M : Machine.{0}) (U₁ U₂ : M.St → ℝ) (a b : M.St),
      (∀ s t : M.St, M.Indist s t → U₁ s = U₁ t) ∧
      (∀ s t : M.St, M.Indist s t → U₂ s = U₂ t) ∧
      U₁ b < U₁ a ∧ U₂ a < U₂ b) ∧
    (∃ C : TwoParty, C.Correspondence ∧ ¬ C.HasChannel) :=
  ⟨structure_does_not_imply_utility, correspondence_does_not_imply_channel⟩

end MetaLang
