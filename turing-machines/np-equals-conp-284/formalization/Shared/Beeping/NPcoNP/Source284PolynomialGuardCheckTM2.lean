import Shared.Beeping.NPcoNP.Source284PolynomialGuardFamily
import Shared.Beeping.NPcoNP.Source284EvaluatorAccept

/-! Execute the input-dependent generated guard with the already verified
unary-clock source evaluator. This proves an actual canonical TM2 polynomial
checker, but not a fixed relative-source compiler or physical refinement. -/
namespace Shared.Beeping.NPcoNP.Source284PolynomialGuardCheckTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284PolynomialGuardFamily
open Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep (Packed)
open Shared.Codes.BitNumeralCompare (value)

abbrev Input := Source284PolynomialGuardFamily.Input × (List Bool × List Bool)

def clockTokens (p time : Polynomial Nat) (x : Source284PolynomialGuardFamily.Input) : List Bool :=
  Source284FixedGuardRowTM2.copies 4 (parameters p time x).1 ++
    (parameters p time x).2.1 ++ List.replicate 11 true

private theorem append_poly {α : Type} [BitstringEncoding α]
    (f g : α → List Bool) (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (fun x => f x ++ g x) := by
  have h := TM2GuardAllStep.pair_isPolyTime f g hf hg
  simpa [TM2ListAppend.append] using TM2Compose.isPolyTime_comp (fun x => (f x,g x))
    (TM2ListAppend.append (α := Bool)) h TM2ListAppend.append_isPolyTime

theorem clockTokens_isPolyTime (p time : Polynomial Nat) : IsPolyTime (clockTokens p time) := by
  let params : Source284PolynomialGuardFamily.Input → Source284FixedGuardTimedTM2.Input := parameters p time
  let witness : Source284PolynomialGuardFamily.Input → List Bool := fun x => (params x).1
  let rest : Source284PolynomialGuardFamily.Input → List Bool × EncRows := fun x => (params x).2
  let ticks : Source284PolynomialGuardFamily.Input → List Bool := fun x => (rest x).1
  let repeated : Source284PolynomialGuardFamily.Input → List Bool := fun x => Source284FixedGuardRowTM2.copies 4 (witness x)
  let eleven : Source284PolynomialGuardFamily.Input → List Bool := fun _ => List.replicate 11 true
  have hp : IsPolyTime params := parameters_isPolyTime p time
  have hw : IsPolyTime witness := TM2Compose.isPolyTime_comp params _ hp TM2PairFirst.first_isPolyTime
  have hr : IsPolyTime rest := TM2Compose.isPolyTime_comp params _ hp TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime ticks := TM2Compose.isPolyTime_comp rest _ hr TM2PairFirst.first_isPolyTime
  have hrep : IsPolyTime repeated := TM2Compose.isPolyTime_comp witness _ hw
    (Source284FixedGuardRowTM2.copies_isPolyTime 4)
  have he : IsPolyTime eleven := by
    have h := TM2Compose.isPolyTime_comp (fun x : Source284PolynomialGuardFamily.Input => x.1)
      (TM2UnaryPolynomialIO.unaryPolynomial (Polynomial.C 11)) TM2PairFirst.first_isPolyTime
      (TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime (Polynomial.C 11))
    simpa [eleven,TM2UnaryPolynomialIO.unaryPolynomial] using h
  have ha := append_poly repeated ticks hrep ht
  have hb := append_poly (fun x => repeated x ++ ticks x) eleven ha he
  change IsPolyTime (fun x => clockTokens p time x)
  simpa [clockTokens,params,witness,rest,ticks,repeated,eleven,List.append_assoc] using hb

theorem clockTokens_length (p time : Polynomial Nat) (x : Source284PolynomialGuardFamily.Input) :
    (clockTokens p time x).length = cutoff p time x := by
  have hd := Source284FixedGuardRewind.duration_exact (limit p x)
  simp only [clockTokens,List.length_append,List.length_replicate,
    Source284FixedGuardRowTM2.copies_length,witness_length,fuel_length,
    cutoff,Source284FixedGuardTimed.time,limit,fuel]
  simp only [limit] at hd
  omega

def packed (p time : Polynomial Nat) (x : Input) : Packed :=
  ((sourceBits p time x.1,(x.2.2,x.2.1)),[true])

theorem packed_isPolyTime (p time : Polynomial Nat) : IsPolyTime (packed p time) := by
  let family : Input → Source284PolynomialGuardFamily.Input := fun x => x.1
  let tapes : Input → List Bool × List Bool := fun x => x.2
  let inputBits : Input → List Bool := fun x => (tapes x).1
  let certBits : Input → List Bool := fun x => (tapes x).2
  let code : Input → List Bool := fun x => sourceBits p time (family x)
  let one : Input → List Bool := fun _ => [true]
  have hf : IsPolyTime family := TM2PairFirst.first_isPolyTime
  have ht : IsPolyTime tapes := TM2GuardAllStep.second_isPolyTime
  have hi : IsPolyTime inputBits := TM2Compose.isPolyTime_comp tapes _ ht TM2PairFirst.first_isPolyTime
  have hc : IsPolyTime certBits := TM2Compose.isPolyTime_comp tapes _ ht TM2GuardAllStep.second_isPolyTime
  have hcode : IsPolyTime code := TM2Compose.isPolyTime_comp family (sourceBits p time) hf
    (sourceBits_isPolyTime p time)
  have hone : IsPolyTime one :=
    TM2GateCNFPieces.singleton_isPolyTime _ (TM2Constant.isPolyTime true)
  exact TM2GuardAllStep.pair_isPolyTime _ one
    (TM2GuardAllStep.pair_isPolyTime code (fun x => (certBits x,inputBits x)) hcode
      (TM2GuardAllStep.pair_isPolyTime certBits inputBits hc hi)) hone

def check (p time : Polynomial Nat) (x : Input) : Bool :=
  Source284EvaluatorAccept.accepts (packed p time x,clockTokens p time x.1)

theorem check_isPolyTime (p time : Polynomial Nat) : IsPolyTime (check p time) := by
  let family : Input → Source284PolynomialGuardFamily.Input := fun x => x.1
  let clock : Input → List Bool := fun x => clockTokens p time (family x)
  have hf : IsPolyTime family := TM2PairFirst.first_isPolyTime
  have ht : IsPolyTime clock := TM2Compose.isPolyTime_comp family (clockTokens p time) hf
    (clockTokens_isPolyTime p time)
  exact TM2Compose.isPolyTime_comp (fun x : Input => (packed p time x,clock x))
    Source284EvaluatorAccept.accepts
    (TM2GuardAllStep.pair_isPolyTime _ _ (packed_isPolyTime p time) ht)
    Source284EvaluatorAccept.accepts_isPolyTime

/-- Exact agreement with the source evaluator, including both the adapter
and the cutoff. Input and certificate are arbitrary binary lists. -/
theorem check_correct (p time : Polynomial Nat) (x : Input) :
    check p time x = Source284Relative.accepts (value (sourceBits p time x.1))
      (value x.2.1) (value x.2.2) (cutoff p time x.1) := by
  rw [check,Source284EvaluatorAccept.accepts_correct,clockTokens_length]
  rfl

/-- Conditional verifier correctness is inherited by the fully executable
polynomial-time checker, for every encoded-certificate alias. -/
theorem check_positive (p time : Polynomial Nat) (x : Input)
    (predicate : List Bool → Bool) (hi : 0 < Source284Parser.length (value x.2.1))
    (hn : 0 < x.1.2.length) (hv : Source284ListTables.valid (decodeRows x.1.2) = true)
    (hmatch : ∀ c w, Source284TaggedWitnessCodec.decode (limit p x.1) c = some w →
      (run (Source284ListTables.table (decodeRows x.1.2)) ⟨c,value x.2.1,some 0⟩
        (fuel time x.1+1)).state.isNone = predicate w) :
    check p time x = Source284TaggedWitnessCodec.check (limit p x.1) predicate (value x.2.2) := by
  rw [check_correct]
  exact positive_check p time x.1 (value x.2.1) (value x.2.2) predicate hi hn hv hmatch

/-- A complete finite certificate search over the executable checker agrees
with the intended bounded witness search. The existential equivalence is
mathematical; it does not claim the exhaustive search itself is polynomial. -/
theorem check_bounded_search (p time : Polynomial Nat)
    (family : Source284PolynomialGuardFamily.Input) (input : List Bool)
    (predicate : List Bool → Bool) (hi : 0 < Source284Parser.length (value input))
    (hn : 0 < family.2.length) (hv : Source284ListTables.valid (decodeRows family.2) = true)
    (hmatch : ∀ c w, Source284TaggedWitnessCodec.decode (limit p family) c = some w →
      (run (Source284ListTables.table (decodeRows family.2)) ⟨c,value input,some 0⟩
        (fuel time family+1)).state.isNone = predicate w) :
    (∃ cert : List Bool, value cert < 2^(cutoff p time family) ∧
      check p time (family,(input,cert)) = true) ↔
      ∃ w, w.length ≤ limit p family ∧ predicate w = true := by
  have hs := positive_bounded_search p time family (value input) 0 predicate hi hn hv hmatch
  simp only [Nat.add_zero] at hs
  rw [← hs,Source284Relative.acceptBound_iff]
  constructor
  · rintro ⟨cert,hbound,hcheck⟩
    exact ⟨value cert,hbound,by simpa only [check_correct] using hcheck⟩
  · rintro ⟨cert,hbound,hcheck⟩
    refine ⟨cert.bits,?_,?_⟩
    · simpa only [Shared.Codes.BinaryAdditionCanonical.value_bits] using hbound
    · simpa only [check_correct,Shared.Codes.BinaryAdditionCanonical.value_bits] using hcheck

/-- The special empty source prefix is accepted even when the supplied
verifier rows are malformed, because the explicit adapter handles it first. -/
theorem check_empty (p time : Polynomial Nat) (x : Input)
    (hi : Source284Parser.length (value x.2.1) = 0) : check p time x = true := by
  rw [check_correct]
  have h := empty_attempt p time x.1 (value x.2.1) (value x.2.2) hi
  have hc : 1 ≤ cutoff p time x.1 := by
    simp only [cutoff,Source284FixedGuardTimed.time]
    omega
  have hm := Source284Relative.accepts_clock_mono (value (sourceBits p time x.1))
    (value x.2.1) (value x.2.2) 1 (cutoff p time x.1-1) h
  have he : 1 + (cutoff p time x.1-1) = cutoff p time x.1 := by omega
  rw [he] at hm
  exact hm

namespace Fixtures

example : (clockTokens Polynomial.X 0 ([],[])).length = 15 := by
  rw [clockTokens_length]
  simp [cutoff,limit,fuel,Source284FixedGuardTimed.time,
    Source284FixedGuardRewind.duration_exact]

example (p time : Polynomial Nat) (cert : List Bool) :
    check p time (([],[]),([],cert)) = true := by
  apply check_empty
  change Source284Parser.length (value ([] : List Bool)) = 0
  decide +kernel

end Fixtures

end Shared.Beeping.NPcoNP.Source284PolynomialGuardCheckTM2
