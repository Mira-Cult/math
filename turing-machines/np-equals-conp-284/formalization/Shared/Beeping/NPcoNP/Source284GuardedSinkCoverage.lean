import Shared.Beeping.NPcoNP.Source284GuardedCoverage
import Shared.Beeping.NPcoNP.Source284ClockStability

/-! Explicit sufficient conditions for the guarded source-verifier coverage
reduction.  These lemmas do not construct the polynomial-time verifier, its
cutoff guard, or its reject sink. -/
namespace Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284Relative

/-- Both finite table entries out of a positive state can be checked directly
from the source's overlapping unary-record encoding. If both return the same
state, the state is invariant for arbitrary tapes and either input symbol. -/
theorem invariant_of_records (description sink : Nat) (hs : 0 < sink)
    (hzero : record description (sink - 1) / 4 = sink)
    (hone : record description sink / 4 = sink) :
    ∀ c : Config, c.state = sink → (step description c).state = sink := by
  intro c hc
  have hm : c.right % 2 = 0 ∨ c.right % 2 = 1 := by omega
  rcases hm with hm | hm
  · simp [step, hc, Nat.ne_of_gt hs, hm, hzero]
    split_ifs <;> rfl
  · have hidx : sink - 1 + 1 = sink := by omega
    simp [step, hc, Nat.ne_of_gt hs, hm, hidx, hone]
    split_ifs <;> rfl

/-- Reaching either state zero or a fixed positive invariant reject state by
cutoff gives the exact positive-prefix stability required for padding. -/
theorem positiveStableAfter_of_sink (description sink : Nat) (p : Polynomial Nat)
    (hsinkne : sink ≠ 0)
    (hsink : ∀ c : Config, c.state = sink → (step description c).state = sink)
    (finished : ∀ i, 0 < Source284Parser.length i → ∀ certificate,
      (run description (initial i certificate) (p.eval (Source284Parser.length i))).state = 0 ∨
      (run description (initial i certificate) (p.eval (Source284Parser.length i))).state = sink) :
    PositiveStableAfter description (fun i => p.eval (Source284Parser.length i)) := by
  intro i hi certificate t ht
  have hs := accepts_stable_at_cutoff description i (p.eval (Source284Parser.length i)) sink
    hsinkne hsink (finished i hi) certificate (t - p.eval (Source284Parser.length i))
  simpa [Nat.add_sub_of_le ht] using hs

/-- A single source verifier with a finite rejecting sink, a proved cutoff,
and correct cutoff-time existential behavior yields a good coupled-clock
candidate. The separate one-step empty-prefix condition remains explicit. -/
theorem good_candidate_of_sink (description sink : Nat) (p : Polynomial Nat)
    (hsinkne : sink ≠ 0)
    (hsink : ∀ c : Config, c.state = sink → (step description c).state = sink)
    (finished : ∀ i, 0 < Source284Parser.length i → ∀ certificate,
      (run description (initial i certificate) (p.eval (Source284Parser.length i))).state = 0 ∨
      (run description (initial i certificate) (p.eval (Source284Parser.length i))).state = sink)
    (correct : ∀ i, 0 < Source284Parser.length i →
      acceptBound description i (p.eval (Source284Parser.length i))
        (2 ^ p.eval (Source284Parser.length i)) = !reference i)
    (empty : ∀ i, Source284Parser.length i = 0 →
      acceptBound description i 1 2 = !reference i) :
    ∃ j, ∀ i, candidate j i = !reference i :=
  padded_good_candidate_of_positive_stable description p
    (positiveStableAfter_of_sink description sink p hsinkne hsink finished) correct empty

end Shared.Beeping.NPcoNP.Source284Comparison
