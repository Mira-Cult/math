import PASoundness.ObserverBridge
import PASoundness.Schedule

/-! Closed receipt-level controls.  These are explicit source-event structures,
not claims about a physical transition table or an executable truth decision. -/

namespace PASoundness.ObserverControls

open PASoundness.Observer

def silent : EventStructure where
  profile := .legacy
  out := fun _ _ _ => False
  error := fun _ => False

theorem silent_incomplete : ¬ Complete silent := by
  intro h
  have ha : Admissible .legacy ⟨1, 0, [0]⟩ := by simp [Admissible]
  cases h.1.2.1 ⟨1, 0, [0]⟩ ha with
  | inl h => obtain ⟨_, hf⟩ := h; exact hf
  | inr h => obtain ⟨_, hf⟩ := h; exact hf

theorem silent_neither (view : ZeroView) :
    ¬ SoundnessAcceptance view silent ∧ ¬ Q_omega view silent :=
  incomplete_neither view silent silent_incomplete

/-- One finite record is insufficient even though its bit is zero and it is legal. -/
def oneRecord : EventStructure where
  profile := .legacy
  out := fun b t a => b = false ∧ t = 0 ∧ a = ⟨1, 0, [0]⟩
  error := fun _ => False

theorem oneRecord_incomplete : ¬ Complete oneRecord := by
  intro h
  have ha : Admissible .legacy ⟨1, 1, [0]⟩ := by simp [Admissible]
  have hout := h.1.2.1 ⟨1, 1, [0]⟩ ha
  simp [Emitted, oneRecord] at hout

/-- Two incompatible completed values at the same address are not a witness
of either soundness or unsoundness. -/
def conflicting : EventStructure where
  profile := .legacy
  out := fun _ _ a => a = ⟨1, 0, [0]⟩
  error := fun _ => False

theorem conflicting_incomplete : ¬ Complete conflicting := by
  intro h
  exact h.1.2.2 ⟨1, 0, [0]⟩ ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩

/-- Every actual source stage answers its prescribed positive-rank key with zero. -/
def scheduledZero : EventStructure where
  profile := .legacy
  out := fun b stage a => b = false ∧ Schedule.scheduledAddress stage = a
  error := fun _ => False

theorem scheduledZero_complete : Complete scheduledZero := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rintro ⟨_, h⟩; exact h
  · intro a ha
    exact Or.inl ⟨Schedule.stageForAddress a 0, rfl,
      Schedule.scheduled_stageForAddress a ha 0⟩
  · rintro a ⟨_, ⟨t, h⟩⟩
    cases h.1
  · intro b t a h
    rw [← h.2]
    exact Schedule.scheduled_admissible t

theorem scheduledZero_agreement :
    RecordsAgree scheduledZero (fun _ _ _ => false) := by
  intro n p xs _ _
  simp [Emitted, scheduledZero]

theorem scheduledZero_no_rank (n : Nat) : ¬ RawFailure scheduledZero n := by
  rintro ⟨p, h⟩
  have heq : altPrefix .all n (fun xs => Emitted scheduledZero true ⟨n, p, xs⟩) ↔
      altPrefix .all n (fun _ => False) :=
    altPrefix_congr_length .all n _ _ (fun xs _ => by simp [Emitted, scheduledZero])
  exact (altPrefix_constant .all n False).mp (heq.mp h)

theorem scheduledZero_no_zero (view : ZeroView) : ¬ RawZero view scheduledZero := by
  cases view with
  | rankZero => exact scheduledZero_no_rank 0
  | compactSuffix =>
    rintro ⟨_, _, ⟨_, h⟩⟩
    cases h.1

theorem scheduledZero_accepted : SoundnessAcceptance .compactSuffix scheduledZero :=
  ⟨scheduledZero_complete, scheduledZero_no_zero .compactSuffix,
    fun n _ => scheduledZero_no_rank n⟩

theorem scheduledZero_no_finite_level : ¬ Q_omega .compactSuffix scheduledZero :=
  ((acceptance_complement_on_complete .compactSuffix scheduledZero).mp
    scheduledZero_accepted).2

def badAddress : Address := ⟨0, 0, []⟩

/-- Add one invalid rank-zero frame to an otherwise complete zero source.
The explicit valid-address guard rejects it even without an Error flag. -/
def invalidExtra : EventStructure where
  profile := .legacy
  out := fun b t a => scheduledZero.out b t a ∨
    (b = false ∧ t = 0 ∧ a = badAddress)
  error := fun _ => False

theorem invalidExtra_basic : BasicComplete invalidExtra := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, h⟩; exact h
  · intro a ha
    exact Or.inl ⟨Schedule.stageForAddress a 0,
      Or.inl ⟨rfl, Schedule.scheduled_stageForAddress a ha 0⟩⟩
  · rintro a ⟨_, ⟨t, h⟩⟩
    cases h with
    | inl h => cases h.1
    | inr h => cases h.1

theorem invalidExtra_incomplete : ¬ Complete invalidExtra := by
  intro h
  have ha := h.2 false 0 badAddress (Or.inr ⟨rfl, rfl, rfl⟩)
  have hpos : 0 < 0 := ha.2 rfl
  omega

def escapingVariable : Formula := .exNat (.natEq (.var 1) .zero)

theorem escapingVariable_rejected : ¬ escapingVariable.Scoped 0 0 0 0 := by
  simp [escapingVariable, Formula.Scoped, NatTerm.Scoped]

end PASoundness.ObserverControls
