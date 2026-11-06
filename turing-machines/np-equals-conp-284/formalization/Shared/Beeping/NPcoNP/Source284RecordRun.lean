import Shared.Beeping.NPcoNP.Source284Relative

/-! Finite-run locality for source descriptions that agree on a prefix of
unary records. The selected record is `state - 1 + readBit`, so the state
bound must be strict. This does not assert that any given program satisfies
the bound, or that increasing a candidate's clock preserves rejection. -/

namespace Shared.Beeping.NPcoNP.Source284Relative

def RecordAgreement (bound a b : Nat) : Prop :=
  ∀ ordinal, ordinal < bound → record a ordinal = record b ordinal

theorem step_eq_of_recordAgreement (bound a b : Nat) (c : Config)
    (hrecords : RecordAgreement bound a b) (hstate : c.state < bound) :
    step a c = step b c := by
  by_cases hz : c.state = 0
  · simp [step, hz]
  · have hr : c.right % 2 < 2 := Nat.mod_lt _ (by decide)
    have hi : c.state - 1 + c.right % 2 < bound := by omega
    simp only [step, hz, if_false, hrecords _ hi]

/-- A finite run is unchanged when all record indices it may consult fit in
the shared prefix. The bound is required for the original run only. -/
theorem run_eq_of_recordAgreement (bound a b : Nat) (c : Config) (clock : Nat)
    (hrecords : RecordAgreement bound a b)
    (hbound : ∀ t, t < clock → (run a c t).state < bound) :
    run a c clock = run b c clock := by
  induction clock with
  | zero => rfl
  | succ clock ih =>
    have ih' := ih (fun t ht => hbound t (by omega))
    rw [run_succ, run_succ, ← ih']
    exact step_eq_of_recordAgreement bound a b _ hrecords (hbound clock (by omega))

theorem accepts_eq_of_recordAgreement (bound a b input certificate clock : Nat)
    (hrecords : RecordAgreement bound a b)
    (hbound : ∀ t, t < clock → (run a (initial input certificate) t).state < bound) :
    accepts a input certificate clock = accepts b input certificate clock := by
  simp only [accepts, run_eq_of_recordAgreement bound a b _ clock hrecords hbound]

end Shared.Beeping.NPcoNP.Source284Relative
