import Shared.Beeping.NPcoNP.Source284Relative

/-! Finite-control bounds for the 284 source's virtual-zero unary records.
The bounds are on numeric source states, not on physical tape space or time.
They do not supply a compiler or a polynomial bit-cost simulation. -/

namespace Shared.Beeping.NPcoNP.Source284Relative

/-- Both the decoded unary count and the remaining code are bounded by the
original natural-number description. -/
theorem readRecord_le (digit : Nat) :
    (readRecord digit).1 ≤ digit ∧ (readRecord digit).2 ≤ digit := by
  induction digit using Nat.strong_induction_on with
  | h digit ih =>
    by_cases ho : digit % 2 = 1
    · have hp : 0 < digit := by omega
      have hlt : digit / 2 < digit := Nat.div_lt_self hp (by decide)
      have hr := ih (digit / 2) hlt
      rw [readRecord_odd digit ho]
      simp only [Prod.fst, Prod.snd]
      constructor <;> omega
    · have he : digit % 2 = 0 := by omega
      rw [readRecord_even digit he]
      simp only [Prod.fst, Prod.snd, Nat.zero_le, true_and]
      exact Nat.div_le_self digit 2

theorem dropRecords_le (digit ordinal : Nat) : dropRecords digit ordinal ≤ digit := by
  induction ordinal generalizing digit with
  | zero => simp [dropRecords]
  | succ ordinal ih =>
    exact le_trans (ih (readRecord digit).2) (readRecord_le digit).2

theorem record_le (description ordinal : Nat) : record description ordinal ≤ description := by
  exact le_trans (readRecord_le (dropRecords description ordinal)).1
    (dropRecords_le description ordinal)

/-- A transition cannot increase the source control beyond the larger of
the old state and one quarter of the fixed description. -/
theorem step_state_le (description : Nat) (c : Config) :
    (step description c).state ≤ max c.state (description / 4) := by
  by_cases hz : c.state = 0
  · simp [step, hz]
  · have hr := record_le description (c.state - 1 + c.right % 2)
    have hq : record description (c.state - 1 + c.right % 2) / 4 ≤ description / 4 :=
      Nat.div_le_div_right hr
    simp only [step, hz, ↓reduceIte]
    split <;> simp_all <;> omega

/-- Every bounded execution remains within one finite control interval. -/
theorem run_state_le (description : Nat) (c : Config) (clock : Nat) :
    (run description c clock).state ≤ max c.state (description / 4) := by
  induction clock with
  | zero => simp [run]
  | succ clock ih =>
    have hs := step_state_le description (run description c clock)
    simp only [run_succ]
    exact le_trans hs (max_le ih (le_max_right _ _))

/-- From the actual source initialization, state 0 and all live states lie
in a finite range determined solely by the fixed description. -/
theorem initial_run_state_le (description input certificate clock : Nat) :
    (run description (initial input certificate) clock).state ≤ max 1 (description / 4) := by
  simpa [initial] using run_state_le description (initial input certificate) clock

end Shared.Beeping.NPcoNP.Source284Relative
