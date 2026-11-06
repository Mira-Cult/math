import Shared.Beeping.NPcoNP.Source284Truncation

/-! Clock extension for the 284 source evaluator.

Acceptance is absorbing, but a timeout may turn into acceptance under a
larger clock.  A verifier wrapper can avoid that problem if, by its original
cutoff, each run is either accepting or in a nonzero absorbing reject state.
The theorems below make that condition explicit and exploit the low-bit
certificate truncation theorem.  They do not construct such a wrapper or
assert that an arbitrary candidate satisfies the condition. -/

namespace Shared.Beeping.NPcoNP.Source284Relative

theorem run_add_clock (description : Nat) (c : Config) (clock extra : Nat) :
    run description c (clock + extra) = run description (run description c clock) extra := by
  induction extra with
  | zero => simp
  | succ extra ih => simp only [Nat.add_succ, run_succ, ih]

/-- Once an attempt accepts, extra source iterations cannot undo it. -/
theorem accepts_clock_mono (description input certificate clock extra : Nat)
    (h : accepts description input certificate clock = true) :
    accepts description input certificate (clock + extra) = true := by
  rw [accepts_iff] at h ⊢
  rw [run_add_clock, run_absorbing _ _ h]
  exact h

/-- A control state that every tape transition preserves remains selected. -/
theorem run_state_invariant (description sink : Nat)
    (hsink : ∀ c : Config, c.state = sink → (step description c).state = sink)
    (c : Config) (hc : c.state = sink) (clock : Nat) :
    (run description c clock).state = sink := by
  induction clock with
  | zero => exact hc
  | succ clock ih => exact hsink _ ih

/-- A cutoff at which every run has accepted or entered the specified
nonaccepting invariant state is stable for every later clock. -/
theorem accepts_stable_at_cutoff (description input cutoff sink : Nat)
    (_hsinkne : sink ≠ 0)
    (hsink : ∀ c : Config, c.state = sink → (step description c).state = sink)
    (hcutoff : ∀ certificate,
      (run description (initial input certificate) cutoff).state = 0 ∨
      (run description (initial input certificate) cutoff).state = sink)
    (certificate extra : Nat) :
    accepts description input certificate (cutoff + extra) =
      accepts description input certificate cutoff := by
  have heq : (run description (initial input certificate) (cutoff + extra)).state =
      (run description (initial input certificate) cutoff).state := by
    rw [run_add_clock]
    rcases hcutoff certificate with hacc | hrej
    · rw [run_absorbing _ _ hacc]
    · rw [run_state_invariant description sink hsink _ hrej extra, hrej]
  simp only [accepts, heq]

/-- Once the cutoff condition holds, neither more time nor more certificate
bits can alter existential acceptance. The larger search must include all
low-`cutoff` representatives, and the original cutoff is retained. -/
theorem acceptBound_stable_at_cutoff (description input cutoff sink : Nat)
    (hsinkne : sink ≠ 0)
    (hsink : ∀ c : Config, c.state = sink → (step description c).state = sink)
    (hcutoff : ∀ certificate,
      (run description (initial input certificate) cutoff).state = 0 ∨
      (run description (initial input certificate) cutoff).state = sink)
    (extra bound : Nat) (hb : 2 ^ cutoff ≤ bound) :
    acceptBound description input (cutoff + extra) bound =
      acceptBound description input cutoff (2 ^ cutoff) := by
  apply Bool.eq_iff_iff.mpr
  rw [acceptBound_iff, acceptBound_iff]
  constructor
  · rintro ⟨certificate, _, haccept⟩
    refine ⟨certificate % 2 ^ cutoff, Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
    rw [← accepts_truncate description input certificate cutoff]
    rw [← accepts_stable_at_cutoff description input cutoff sink hsinkne hsink hcutoff certificate extra]
    exact haccept
  · rintro ⟨certificate, hc, haccept⟩
    refine ⟨certificate, lt_of_lt_of_le hc hb, ?_⟩
    rw [accepts_stable_at_cutoff description input cutoff sink hsinkne hsink hcutoff certificate extra]
    exact haccept

/-- Some stability condition is needed in general: extending the clock and
the certificate bound can turn a rejecting bounded search into acceptance. -/
theorem longer_clock_can_accept :
    acceptBound 31 2 1 2 = false ∧ acceptBound 31 2 2 4 = true := by
  simp [acceptBound, accepts, run, initial, step, record, dropRecords, readRecord]
  exact ⟨0, by decide⟩

end Shared.Beeping.NPcoNP.Source284Relative
