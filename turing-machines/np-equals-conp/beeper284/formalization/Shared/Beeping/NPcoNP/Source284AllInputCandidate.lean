import Shared.Beeping.NPcoNP.Source284EmptyPrefixWrapper
import Shared.Beeping.NPcoNP.Source284MarkedCanonicalNP
import Shared.Beeping.NPcoNP.Source284PositiveClock
import Shared.Beeping.NPcoNP.Source284RunPadding

/-! Full candidate coverage of canonical NP languages, including the
one-step zero-prefix boundary. The code exponent and source program remain
coupled, and the two entry turns are charged on positive inputs. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284AllInputCandidate

open ComplexityTheory
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

theorem empty_bounded_acceptance (emptyValue : Bool) (original input : Nat) (heven : input%2=0) :
    acceptBound (Source284EmptyPrefixWrapper.description emptyValue original) input 1 2 = emptyValue := by
  cases emptyValue with
  | false =>
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨certificate,_,ha⟩ := (acceptBound_iff _ _ _ _).1 h
    have hn := Source284EmptyPrefixWrapper.empty_accepts false original input certificate heven
    rw [hn] at ha
    contradiction
  | true =>
    apply (acceptBound_iff _ _ _ _).2
    exact ⟨0,by decide,Source284EmptyPrefixWrapper.empty_accepts true original input 0 heven⟩

theorem frame_odd (x : List Bool) (suffix : Nat) (hx : 0 < x.length) :
    encodeFrame x suffix%2=1 := by
  cases x with
  | nil => simp at hx
  | cons b xs => cases b <;> simp [encodeFrame] <;> omega

/-- Every canonical NP language has one arbitrarily large coupled source
candidate agreeing on all framed inputs, including empty frames and all
high-suffix aliases. -/
theorem canonical_np_all_input_candidate (L : DecisionProblem)
    (hL : L ∈ ComplexityTheory.NP) (threshold : Nat) :
    ∃ j : Nat, threshold < j ∧ ∀ (x : List Bool) (suffix : Nat),
      (candidate j (encodeFrame x suffix) = true ↔ L x = true) := by
  obtain ⟨original,k,time,bits,cutoff,_,hcoverage,hsound⟩ :=
    Source284MarkedCanonicalNP.canonical_np_source L hL
  let wrapped := Source284EmptyPrefixWrapper.description (L []) original
  obtain ⟨exponent,hexponent⟩ := positive_prefix_polynomial_bound (time+bits+2)
  obtain ⟨j,hj,hpad⟩ := exists_larger_preserving_bounded_acceptance wrapped (max exponent threshold)
  have hjk : exponent ≤ j := by omega
  refine ⟨j,by omega,?_⟩
  intro x suffix
  by_cases hx : x=[]
  · subst x
    have heven : encodeFrame [] suffix%2=0 := by simp [encodeFrame]
    have hlength : Source284Parser.length (encodeFrame [] suffix)=0 := by
      simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
    have hclock : clock j (encodeFrame [] suffix)=1 := clock_empty_prefix j _ hlength
    have he := empty_bounded_acceptance (L []) original (encodeFrame [] suffix) heven
    unfold candidate
    rw [hclock,← hpad (encodeFrame [] suffix) 1 (2^1)]
    simpa [wrapped] using congrArg (fun b : Bool => b = true) he
  · have hxpos : 0 < x.length := by cases x <;> simp_all
    let input := encodeFrame x suffix
    have hodd : input%2=1 := frame_odd x suffix hxpos
    have hlength : Source284Parser.length input = x.length := by
      simp [input,Source284Parser.length,Source284Parser.parse_encodeFrame]
    have hclock := hexponent j input hjk (by simpa [hlength] using hxpos)
    have htime : time.eval x.length+2 ≤ clock j input := by
      simp only [hlength,Polynomial.eval_add,Polynomial.eval_ofNat] at hclock
      omega
    have hbits : bits.eval x.length ≤ clock j input := by
      simp only [hlength,Polynomial.eval_add,Polynomial.eval_ofNat] at hclock
      omega
    have htwo : 2 ≤ clock j input := by omega
    have heq : clock j input = 2+(clock j input-2) := by omega
    constructor
    · intro hcandidate
      have hlarge : acceptBound wrapped input (clock j input) (2^clock j input) = true := by
        rw [hpad]
        exact hcandidate
      obtain ⟨certificate,_,haccept⟩ := (acceptBound_iff _ _ _ _).1 hlarge
      have ha : accepts original input certificate (clock j input-2) = true := by
        rw [heq] at haccept
        exact (Source284EmptyPrefixWrapper.positive_accepts (L []) original input certificate _ hodd).symm.trans haccept
      exact hsound x suffix certificate _ ha
    · intro hmem
      have hsmall := hcoverage x suffix hmem
      obtain ⟨certificate,hcert,haccept⟩ := (acceptBound_iff _ _ _ _).1 hsmall
      have hbound : 2^bits.eval x.length ≤ 2^clock j input := Nat.pow_le_pow_right (by decide) hbits
      have hwrapped : accepts wrapped input certificate (2+time.eval x.length) = true := by
        rw [Source284EmptyPrefixWrapper.positive_accepts (L []) original input certificate _ hodd]
        exact haccept
      have hlarge : acceptBound wrapped input (clock j input) (2^clock j input) = true :=
        (acceptBound_iff _ _ _ _).2 ⟨certificate,lt_of_lt_of_le hcert hbound,
          accepts_clock_mono_le _ _ _ _ _ htime (by simpa [Nat.add_comm] using hwrapped)⟩
      unfold candidate
      rw [← hpad input (clock j input) (2^clock j input)]
      exact hlarge

end Shared.Beeping.NPcoNP.Source284AllInputCandidate
