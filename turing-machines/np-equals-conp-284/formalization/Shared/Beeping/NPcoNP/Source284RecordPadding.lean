import Shared.Beeping.NPcoNP.Source284RecordEncoding
import Shared.Beeping.NPcoNP.Source284RecordRun

/-! Increasing a source program's numeric description while retaining its
finite record prefix. This does not establish any program's state bound or
the effect of enlarging its clock. -/

namespace Shared.Beeping.NPcoNP.Source284Relative

/-- Any source program has arbitrarily large descriptions with the same
first `bound` unary records. -/
theorem exists_larger_with_records (original bound threshold : Nat) :
    ∃ padded > threshold, RecordAgreement bound original padded := by
  let values : List Nat := List.ofFn (fun i : Fin bound => record original i.val)
  obtain ⟨padded, hp, heq⟩ := records_unbounded values threshold
  refine ⟨padded, hp, ?_⟩
  intro ordinal hordinal
  have hi : ordinal < values.length := by simpa [values] using hordinal
  have := heq ordinal hi
  simpa [values] using this.symm

/-- The same padded description preserves all finite runs whose source
states remain inside the retained prefix, uniformly in input and clock. -/
theorem exists_larger_preserving_runs (original bound threshold : Nat) :
    ∃ padded > threshold, ∀ c clock,
      (∀ t, t < clock → (run original c t).state < bound) →
      run original c clock = run padded c clock := by
  obtain ⟨padded, hp, ha⟩ := exists_larger_with_records original bound threshold
  exact ⟨padded, hp, fun c clock hb =>
    run_eq_of_recordAgreement bound original padded c clock ha hb⟩

end Shared.Beeping.NPcoNP.Source284Relative
