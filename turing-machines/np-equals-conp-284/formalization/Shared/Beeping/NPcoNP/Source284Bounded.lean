import Shared.Beeping.NPcoNP.Source284Relative

/-! Clock and exhaustive-search facts for the bounded source evaluator.
Acceptance is absorbing; timeout and an initially empty certificate range
are ordinary Boolean rejection. -/
namespace Shared.Beeping.NPcoNP.Source284Relative

theorem run_add (description : Nat) (c : Config) (m n : Nat) :
    run description c (m + n) = run description (run description c m) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run, ih]

/-- A bounded attempt accepts exactly when state zero is reached at or
before its boundary. Remaining source iterations are silent state stutters. -/
theorem accepts_iff_reached (description input certificate clock : Nat) :
    accepts description input certificate clock = true ↔
      ∃ t ≤ clock, (run description (initial input certificate) t).state = 0 := by
  rw [accepts_iff]
  constructor
  · intro h
    exact ⟨clock, le_rfl, h⟩
  · rintro ⟨t, ht, hzero⟩
    have hadd : t + (clock - t) = clock := Nat.add_sub_of_le ht
    rw [← hadd, run_add, run_absorbing _ _ hzero]
    exact hzero

theorem accepts_clock_mono_le (description input certificate small large : Nat)
    (h : small ≤ large) (ha : accepts description input certificate small = true) :
    accepts description input certificate large = true := by
  apply (accepts_iff_reached _ _ _ _).2
  obtain ⟨t, ht, hz⟩ := (accepts_iff_reached _ _ _ _).1 ha
  exact ⟨t, le_trans ht h, hz⟩

theorem acceptBound_mono (description input clock small large : Nat)
    (h : small ≤ large) (ha : acceptBound description input clock small = true) :
    acceptBound description input clock large = true := by
  apply (acceptBound_iff _ _ _ _).2
  obtain ⟨certificate, hc, ha⟩ := (acceptBound_iff _ _ _ _).1 ha
  exact ⟨certificate, Nat.lt_of_lt_of_le hc h, ha⟩

/-- The source tries candidates in descending order. Existential Boolean
search gives the same result in the ascending executable implementation. -/
theorem acceptBound_descending (description input clock bound : Nat) :
    acceptBound description input clock bound =
      ((List.range bound).reverse.any fun certificate => accepts description input certificate clock) := by
  simp [acceptBound]

end Shared.Beeping.NPcoNP.Source284Relative
