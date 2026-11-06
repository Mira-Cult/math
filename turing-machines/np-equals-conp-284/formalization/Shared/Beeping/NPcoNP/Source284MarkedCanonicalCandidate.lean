import Shared.Beeping.NPcoNP.Source284MarkedCanonicalNP
import Shared.Beeping.NPcoNP.Source284PositiveClock
import Shared.Beeping.NPcoNP.Source284RunPadding

/-! Unconditional positive-input candidate coverage for every canonical NP
language. Empty decoded inputs and the physical controller remain separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284MarkedCanonicalCandidate

open ComplexityTheory
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

/-- For every canonical NP language and every threshold, a larger single
source candidate agrees on all positive-length framed inputs. -/
theorem canonical_np_positive_candidate (L : DecisionProblem)
    (hL : L ∈ ComplexityTheory.NP) (threshold : Nat) :
    ∃ j : Nat, threshold < j ∧ ∀ (x : List Bool) (suffix : Nat), 0 < x.length →
      (candidate j (encodeFrame x suffix) = true ↔ L x = true) := by
  obtain ⟨description,k,time,bits,cutoff,_,hcoverage,hsound⟩ :=
    Source284MarkedCanonicalNP.canonical_np_source L hL
  obtain ⟨exponent,hexponent⟩ := positive_prefix_polynomial_bound (time+bits)
  obtain ⟨j,hj,hpad⟩ := exists_larger_preserving_bounded_acceptance description (max exponent threshold)
  have hjk : exponent ≤ j := by omega
  refine ⟨j,by omega,?_⟩
  intro x suffix hx
  constructor
  · intro hcandidate
    have hlarge : acceptBound description (encodeFrame x suffix)
        (clock j (encodeFrame x suffix)) (2^clock j (encodeFrame x suffix)) = true := by
      rw [hpad]
      exact hcandidate
    obtain ⟨certificate,_,haccept⟩ := (acceptBound_iff _ _ _ _).1 hlarge
    exact hsound x suffix certificate _ haccept
  · intro hmem
    let input := encodeFrame x suffix
    have hlength : Source284Parser.length input = x.length := by
      simp [input,Source284Parser.length,Source284Parser.parse_encodeFrame]
    have hclock := hexponent j input hjk (by simpa [hlength] using hx)
    have htime : time.eval x.length ≤ clock j input := by
      simp only [hlength,Polynomial.eval_add] at hclock
      omega
    have hbits : bits.eval x.length ≤ clock j input := by
      simp only [hlength,Polynomial.eval_add] at hclock
      omega
    have hsmall := hcoverage x suffix hmem
    obtain ⟨certificate,hcert,haccept⟩ := (acceptBound_iff _ _ _ _).1 hsmall
    have hbound : 2^bits.eval x.length ≤ 2^clock j input := Nat.pow_le_pow_right (by decide) hbits
    have hlarge : acceptBound description input (clock j input) (2^clock j input) = true :=
      (acceptBound_iff _ _ _ _).2 ⟨certificate,lt_of_lt_of_le hcert hbound,
        accepts_clock_mono_le _ _ _ _ _ htime haccept⟩
    unfold candidate
    rw [← hpad input (clock j input) (2^clock j input)]
    exact hlarge

end Shared.Beeping.NPcoNP.Source284MarkedCanonicalCandidate
