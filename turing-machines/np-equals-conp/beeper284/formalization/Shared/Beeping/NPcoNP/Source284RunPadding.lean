import Shared.Beeping.NPcoNP.Source284FiniteRecordBounds
import Shared.Beeping.NPcoNP.Source284RecordPadding

/-! Padding that preserves every source attempt from its standard initial
state. This is an extensional statement at the *same supplied* clock and
certificate bound. The source ties a candidate's clock to its numeric
description, so this alone does not establish candidate coverage. -/

namespace Shared.Beeping.NPcoNP.Source284Relative

/-- Every source description has arbitrarily large descriptions that agree
on its entire execution from standard initial states, at every finite clock. -/
theorem exists_larger_preserving_initial_runs (original threshold : Nat) :
    ∃ padded > threshold, ∀ input certificate clock,
      run original (initial input certificate) clock =
        run padded (initial input certificate) clock := by
  obtain ⟨padded, hp, heq⟩ :=
    exists_larger_preserving_runs original (max 1 (original / 4) + 1) threshold
  refine ⟨padded, hp, ?_⟩
  intro input certificate clock
  apply heq
  intro t ht
  have h := initial_run_state_le original input certificate t
  omega

/-- The same padding preserves existential acceptance for every common
input, finite clock, and finite certificate-search bound. -/
theorem exists_larger_preserving_bounded_acceptance (original threshold : Nat) :
    ∃ padded > threshold, ∀ input clock certificateBound,
      acceptBound original input clock certificateBound =
        acceptBound padded input clock certificateBound := by
  obtain ⟨padded, hp, heq⟩ := exists_larger_preserving_initial_runs original threshold
  refine ⟨padded, hp, ?_⟩
  intro input clock certificateBound
  simp only [acceptBound, accepts]
  congr 1
  funext certificate
  rw [heq input certificate clock]

end Shared.Beeping.NPcoNP.Source284Relative
