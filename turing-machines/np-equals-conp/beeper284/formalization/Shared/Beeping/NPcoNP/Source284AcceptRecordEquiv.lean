import Shared.Beeping.NPcoNP.Source284RecordEncoding
import Shared.Beeping.NPcoNP.Source284FiniteRecordBounds

/-! Acceptance-preserving record changes for the selected 284 source.
Two programs may differ on a record when both alternatives go directly to
accepting state zero. Their written bits or turn directions may differ; the
resulting tapes need not agree. This is a semantic lemma, not a complexity or
physical-machine theorem. -/
namespace Shared.Beeping.NPcoNP.Source284Relative

/-- For each record, either the records agree exactly or both records accept
immediately regardless of their different write and turn bits. -/
def AcceptRecordAgreement (a b : Nat) : Prop :=
  ∀ i, record a i = record b i ∨
    (record a i / 4 = 0 ∧ record b i / 4 = 0)

/-- An active transition's state field is exactly the high part of its
selected unary record, regardless of the chosen movement branch. -/
theorem active_step_state (d : Nat) (c : Config) (h : c.state ≠ 0) :
    (step d c).state = record d (c.state - 1 + c.right % 2) / 4 := by
  simp only [step, h, ↓reduceIte]
  split_ifs <;> rfl

/-- Either both attempts have already accepted, or the entire current
configurations are still equal. -/
def AcceptRelated (a b : Config) : Prop :=
  (a.state = 0 ∧ b.state = 0) ∨ a = b

theorem acceptRelated_step (a b : Nat) (h : AcceptRecordAgreement a b)
    (ca cb : Config) (hc : AcceptRelated ca cb) :
    AcceptRelated (step a ca) (step b cb) := by
  rcases hc with (⟨ha,hb⟩ | heq)
  · left
    simp [ha, hb]
  · subst cb
    by_cases hz : ca.state = 0
    · left
      simp [hz]
    · let i := ca.state - 1 + ca.right % 2
      rcases h i with (hr | ⟨ha,hb⟩)
      · right
        simp only [step, hz, ↓reduceIte]
        rw [hr]
      · left
        rw [active_step_state a ca hz, active_step_state b ca hz]
        exact ⟨ha,hb⟩

theorem acceptRelated_run (a b : Nat) (h : AcceptRecordAgreement a b)
    (c : Config) (n : Nat) : AcceptRelated (run a c n) (run b c n) := by
  induction n with
  | zero => exact Or.inr rfl
  | succ n ih =>
    simp only [run_succ]
    exact acceptRelated_step a b h _ _ ih

/-- Equivalent records preserve the acceptance bit at every supplied clock,
including after the two accepting transitions wrote different tape cells. -/
theorem accepts_eq_of_acceptRecordAgreement (a b : Nat) (h : AcceptRecordAgreement a b)
    (input certificate clock : Nat) :
    accepts a input certificate clock = accepts b input certificate clock := by
  have hr := acceptRelated_run a b h (initial input certificate) clock
  rcases hr with (⟨ha,hb⟩ | heq)
  · simp [accepts, ha, hb]
  · simp [accepts, heq]

/-- All bounded certificate searches agree when their finite bound and clock
are the same. The theorem does not equate searches at larger coupled clocks. -/
theorem acceptBound_eq_of_acceptRecordAgreement (a b : Nat) (h : AcceptRecordAgreement a b)
    (input clock bound : Nat) :
    acceptBound a input clock bound = acceptBound b input clock bound := by
  simp only [acceptBound]
  congr 1
  funext certificate
  exact accepts_eq_of_acceptRecordAgreement a b h input certificate clock

/-- Beyond an encoded finite prefix, record lookup continues at the supplied
high tail, including the source's infinite virtual-zero extension. -/
theorem record_encodeRecords_tail (values : List Nat) (tail ordinal : Nat) :
    record (encodeRecords values tail) (values.length + ordinal) = record tail ordinal := by
  induction values with
  | nil => simp [encodeRecords]
  | cons value values ih =>
    simp only [List.length_cons, Nat.succ_add, encodeRecords]
    unfold record at *
    simp only [dropRecords, readRecord_encodeRecord, Prod.snd]
    exact ih

/-- A single high sentinel has only one nonzero record, of value one; every
record in that tail therefore goes immediately to accepting state zero. -/
theorem record_one_accepting (ordinal : Nat) : record 1 ordinal / 4 = 0 := by
  have h := record_le 1 ordinal
  omega

/-- Adding one high sentinel after a finite prefix preserves all record
behavior up to acceptance. In particular a virtual zero and the record one
may write different bits, but both enter accepting state zero immediately. -/
theorem sentinel_acceptRecordAgreement (values : List Nat) :
    AcceptRecordAgreement (encodeRecords values 0) (encodeRecords values 1) := by
  intro i
  by_cases h : i < values.length
  · left
    rw [record_encodeRecords values 0 i h, record_encodeRecords values 1 i h]
  · right
    have hi : values.length ≤ i := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [record_encodeRecords_tail, record_encodeRecords_tail]
    simp [record_one_accepting]

/-- The high-sentinel encoding of a finite record list and the no-sentinel
encoding have the same bounded acceptance bit at every common clock. -/
theorem sentinel_acceptBound (values : List Nat) (input clock bound : Nat) :
    acceptBound (encodeRecords values 0) input clock bound =
      acceptBound (encodeRecords values 1) input clock bound :=
  acceptBound_eq_of_acceptRecordAgreement _ _ (sentinel_acceptRecordAgreement values)
    input clock bound

end Shared.Beeping.NPcoNP.Source284Relative
