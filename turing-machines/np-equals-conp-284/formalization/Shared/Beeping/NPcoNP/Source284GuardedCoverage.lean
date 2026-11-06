import Shared.Beeping.NPcoNP.Source284PositiveClock
import Shared.Beeping.NPcoNP.Source284RunPadding
import Shared.Beeping.NPcoNP.Source284Truncation

/-! A source-specific conditional padding theorem.  The explicit premise
`StableAfter` must be established for an actual timeout-guarded verifier; an
arbitrary source program need not satisfy it.  This module does not implement
that guard or claim canonical NP coverage. -/

namespace Shared.Beeping.NPcoNP.Source284Comparison

open Shared.Beeping.NPcoNP.Source284Relative

/-- After the cutoff, running longer cannot change any individual witness
attempt. In particular, attempts rejected at the cutoff must not accept later. -/
def StableAfter (description : Nat) (cutoff : Nat → Nat) : Prop :=
  ∀ i certificate t, cutoff i ≤ t →
    accepts description i certificate t = accepts description i certificate (cutoff i)

/-- The weaker condition actually needed for coverage. Empty-prefix behavior
is separately handled by the one-step clock and need not stabilize at the
polynomial's value on zero. -/
def PositiveStableAfter (description : Nat) (cutoff : Nat → Nat) : Prop :=
  ∀ i, 0 < Source284Parser.length i → ∀ certificate t, cutoff i ≤ t →
    accepts description i certificate t = accepts description i certificate (cutoff i)

/-- If the polynomial vanishes at zero, the stronger all-input contract would
force the empty-prefix input to reject at its one-step clock. This shows why
the positive-input contract is needed for a correct complement verifier. -/
theorem global_stability_zero_contradicts_empty (description : Nat) (p : Polynomial Nat)
    (hp : p.eval 0 = 0)
    (stable : StableAfter description (fun i => p.eval (Source284Parser.length i)))
    (empty : ∀ i, Source284Parser.length i = 0 →
      acceptBound description i 1 2 = !reference i) : False := by
  have hz : Source284Parser.length 0 = 0 := by
    simp [Source284Parser.length, parse_zero]
  have ha (certificate : Nat) : accepts description 0 certificate 1 = false := by
    have h := stable 0 certificate 1 (by simp [hz, hp])
    simpa [hz, hp] using h
  have hr : reference 0 = false := by
    simp [reference, Source284Parser.length, Source284Parser.description, parse_zero]
  have he := empty 0 hz
  simp [acceptBound, ha, hr] at he

/-- Stability of individual attempts and finite influence of certificate bits
jointly prevent a larger clock and witness range from adding an acceptance. -/
theorem stable_acceptBound (description input short long : Nat)
    (hle : short ≤ long)
    (stable : ∀ certificate,
      accepts description input certificate long = accepts description input certificate short) :
    acceptBound description input long (2^long) =
      acceptBound description input short (2^short) := by
  unfold acceptBound
  simp_rw [stable]
  apply Shared.Beeping.NPcoNP.Source284Parser.range_any_oversupply short (2^long)
  · exact Nat.pow_le_pow_right (by decide) hle
  · intro b
    exact accepts_truncate description input b short

/-- A time-stable source verifier can be padded to a single arbitrarily large
candidate number while preserving its cutoff-time existential result on every
positive-prefix input.  Empty-prefix inputs use the actual one-step clock. -/
theorem padded_candidate_of_positive_stable (description threshold : Nat) (p : Polynomial Nat)
    (stable : PositiveStableAfter description (fun i => p.eval (Source284Parser.length i))) :
    ∃ j > threshold, (∀ i, 0 < Source284Parser.length i →
      candidate j i = acceptBound description i (p.eval (Source284Parser.length i))
        (2 ^ p.eval (Source284Parser.length i))) ∧
      (∀ i, Source284Parser.length i = 0 →
        candidate j i = acceptBound description i 1 2) := by
  obtain ⟨k, hk⟩ := positive_prefix_polynomial_bound p
  obtain ⟨j, hj, hpad⟩ := exists_larger_preserving_bounded_acceptance description (max k threshold)
  have hjk : k ≤ j := by omega
  have hjt : threshold < j := by omega
  refine ⟨j, hjt, ?_, ?_⟩
  · intro i hi
    have hle : p.eval (Source284Parser.length i) ≤ clock j i := hk j i hjk hi
    unfold candidate
    rw [← hpad i (clock j i) (2^clock j i)]
    exact stable_acceptBound description i _ _ hle (fun certificate => stable i hi certificate _ hle)
  · intro i hi
    unfold candidate
    rw [clock_empty_prefix j i hi]
    simpa using (hpad i 1 2).symm

/-- To establish candidate coverage it remains to implement a source verifier
whose cutoff-time witness language is the desired complement and whose
attempts are stable after that cutoff.  The one-step empty-prefix condition is
separate and cannot be absorbed into an exponent. -/
theorem padded_good_candidate_of_positive_stable (description : Nat) (p : Polynomial Nat)
    (stable : PositiveStableAfter description (fun i => p.eval (Source284Parser.length i)))
    (correct : ∀ i, 0 < Source284Parser.length i →
      acceptBound description i (p.eval (Source284Parser.length i))
        (2 ^ p.eval (Source284Parser.length i)) = !reference i)
    (empty : ∀ i, Source284Parser.length i = 0 →
      acceptBound description i 1 2 = !reference i) :
    ∃ j, ∀ i, candidate j i = !reference i := by
  obtain ⟨j, _, hpositive, hempty⟩ := padded_candidate_of_positive_stable description 0 p stable
  refine ⟨j, ?_⟩
  intro i
  by_cases h : Source284Parser.length i = 0
  · exact (hempty i h).trans (empty i h)
  · have hi : 0 < Source284Parser.length i := by omega
    exact (hpositive i hi).trans (correct i hi)

/-- The original all-input stability contract implies the positive-input
contract; retained as an API for earlier consumers. -/
theorem padded_candidate_of_stable (description threshold : Nat) (p : Polynomial Nat)
    (stable : StableAfter description (fun i => p.eval (Source284Parser.length i))) :
    ∃ j > threshold, (∀ i, 0 < Source284Parser.length i →
      candidate j i = acceptBound description i (p.eval (Source284Parser.length i))
        (2 ^ p.eval (Source284Parser.length i))) ∧
      (∀ i, Source284Parser.length i = 0 →
        candidate j i = acceptBound description i 1 2) :=
  padded_candidate_of_positive_stable description threshold p (fun i _ => stable i)

theorem padded_good_candidate_of_stable (description : Nat) (p : Polynomial Nat)
    (stable : StableAfter description (fun i => p.eval (Source284Parser.length i)))
    (correct : ∀ i, 0 < Source284Parser.length i →
      acceptBound description i (p.eval (Source284Parser.length i))
        (2 ^ p.eval (Source284Parser.length i)) = !reference i)
    (empty : ∀ i, Source284Parser.length i = 0 →
      acceptBound description i 1 2 = !reference i) :
    ∃ j, ∀ i, candidate j i = !reference i :=
  padded_good_candidate_of_positive_stable description p (fun i _ => stable i) correct empty

end Shared.Beeping.NPcoNP.Source284Comparison
