import Shared.PNP.Record285.ReferenceChoiceStep
import Shared.Beeping.NPcoNP.Source284EvaluatorBitGrowth

/-! Resource bounds for the choice-aware 285 source evaluator. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ReferenceChoiceGrowth
open Shared.ComplexityBridge
open Shared.PNP.Record285.ReferenceChoiceStep
open Shared.Beeping.NPcoNP
open Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep
open Shared.Beeping.NPcoNP.Source284EvaluatorBitStep
open Shared.Beeping.NPcoNP.Source284EvaluatorBitGrowth
open Shared.Beeping.NPcoNP.Source284UnaryCountBits

def tapeLength (p : Input) : Nat := (left (base p)).length + (right (base p)).length

theorem increment_length (xs : List Bool) : (incrementData xs).length ≤ xs.length + 1 := by
  rw [incrementData_eq]
  exact Shared.Codes.BitTableValidation.increment_length xs

theorem extraState_length (p : Input) :
    (extraState p).length ≤ (state (base p)).length + 2 := by
  unfold extraState
  split_ifs
  · have h1 := increment_length (state (base p))
    have h2 := increment_length (incrementData (state (base p)))
    omega
  · omega

theorem newRight_length (p : Input) : (newRight p).length ≤ (right (base p)).length + 1 := by
  simp only [newRight,List.length_cons,List.length_tail]
  omega

theorem step_tape (p : Input) : tapeLength (ReferenceChoiceStep.step p) ≤ tapeLength p + 2 := by
  by_cases hz : zero (base p) = true
  · simp [ReferenceChoiceStep.step,hz]
  · have h := Source284EvaluatorBitGrowth.step_tapeLength (code (prepared p)) (config (prepared p))
    rw [← config_step] at h
    have hr := newRight_length p
    change (left (Source284EvaluatorPackedStep.step (prepared p))).length +
        (right (Source284EvaluatorPackedStep.step (prepared p))).length ≤
      (left (base p)).length + (newRight p).length + 1 at h
    change tapeLength (ReferenceChoiceStep.step p) ≤ tapeLength p + 2
    rw [ReferenceChoiceStep.step,if_neg hz]
    simp only [tapeLength,base]
    simp only [base] at h hr
    omega

theorem step_state (p : Input) : (state (base (ReferenceChoiceStep.step p))).length ≤
    max (state (base p)).length (code (base p)).length + 2 := by
  by_cases hz : zero (base p) = true
  · simp only [ReferenceChoiceStep.step,hz,if_true]
    have hm := le_max_left (state (base p)).length (code (base p)).length
    omega
  · have h := Source284EvaluatorBitGrowth.step_stateLength (code (prepared p)) (config (prepared p))
    rw [← config_step] at h
    have he := extraState_length p
    change (state (Source284EvaluatorPackedStep.step (prepared p))).length ≤
      max (extraState p).length (code (base p)).length at h
    rw [ReferenceChoiceStep.step,if_neg hz]
    change (state (Source284EvaluatorPackedStep.step (prepared p))).length ≤ _
    have hm : max (extraState p).length (code (base p)).length ≤
        max (state (base p)).length (code (base p)).length + 2 := by
      apply max_le
      · have := le_max_left (state (base p)).length (code (base p)).length
        omega
      · have := le_max_right (state (base p)).length (code (base p)).length
        omega
    exact le_trans h hm

theorem step_choices (p : Input) : (choices (ReferenceChoiceStep.step p)).length ≤ (choices p).length := by
  unfold ReferenceChoiceStep.step
  split_ifs
  · rfl
  · change (choices p).tail.length ≤ (choices p).length
    simp only [List.length_tail]
    omega

/-- All components of each finite prefix have explicit linear bounds; the
program is retained byte for byte and the choice suffix never grows. -/
theorem run_lengths (p : Input) (n : Nat) :
    let q := TM2UnaryIterate.run ReferenceChoiceStep.step p n
    tapeLength q ≤ tapeLength p + 2*n ∧
    (state (base q)).length ≤ max (state (base p)).length (code (base p)).length + 2*n ∧
    (choices q).length ≤ (choices p).length ∧ code (base q) = code (base p) := by
  induction n generalizing p with
  | zero => simp [TM2UnaryIterate.run]
  | succ n ih =>
    simp only [TM2UnaryIterate.run]
    obtain ⟨ht,hs,hch,hcode⟩ := ih (ReferenceChoiceStep.step p)
    have ht' := step_tape p
    have hs' := step_state p
    have hch' := step_choices p
    have hc := code_step p
    rw [hc] at hs hcode
    have hm : max (state (base (ReferenceChoiceStep.step p))).length (code (base p)).length ≤
        max (state (base p)).length (code (base p)).length + 2 := by
      apply max_le
      · exact hs'
      · have := le_max_right (state (base p)).length (code (base p)).length
        omega
    exact ⟨by omega,by omega,by omega,hcode⟩

theorem input_encoded_length (p : Input) :
    (BitstringEncoding.bitEncode p).length =
      24*(code (base p)).length + 24*(left (base p)).length +
      12*(right (base p)).length + 6*(state (base p)).length +
      3*(choices p).length + 11 := by
  rcases p with ⟨⟨⟨code,⟨l,r⟩⟩,s⟩,ch⟩
  change (BitstringEncoding.delimit
    (BitstringEncoding.delimit
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode code) ++
        (BitstringEncoding.delimit (BitstringEncoding.bitEncode l) ++ BitstringEncoding.bitEncode r)) ++
      BitstringEncoding.bitEncode s) ++ BitstringEncoding.bitEncode ch).length = _
  simp only [List.length_append,BitstringEncoding.length_delimit,bitstring_list_encoded_length,
    base,choices,Source284EvaluatorPackedStep.code,left,right,state]
  omega

/-- A single linear polynomial bounds the serialized state at every prefix
by the size of the complete initial data and unary clock. -/
theorem prefix_encoded_bound (p : Input) (clock pref tail : List Bool)
    (hclock : clock = pref ++ tail) :
    (BitstringEncoding.bitEncode
      (TM2PolynomialFold.fold (TM2UnaryIterate.foldStep ReferenceChoiceStep.step) (p,[]) pref)).length ≤
      (Polynomial.C 64 * Polynomial.X).eval (BitstringEncoding.bitEncode (p,clock)).length := by
  rw [TM2UnaryIterate.fold_value]
  have hlen : pref.length ≤ clock.length := by rw [hclock,List.length_append]; omega
  obtain ⟨ht,hs,hch,hcode⟩ := run_lengths p pref.length
  have hm : max (state (base p)).length (code (base p)).length ≤
      (state (base p)).length + (code (base p)).length := max_le (by omega) (by omega)
  have hs' : (state (base (TM2UnaryIterate.run ReferenceChoiceStep.step p pref.length))).length ≤
      (state (base p)).length + (code (base p)).length + 2*pref.length := by omega
  change (BitstringEncoding.delimit (BitstringEncoding.bitEncode
      (TM2UnaryIterate.run ReferenceChoiceStep.step p pref.length)) ++
      BitstringEncoding.bitEncode ([] : List Bool)).length ≤
    (Polynomial.C 64 * Polynomial.X).eval
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode p) ++ BitstringEncoding.bitEncode clock).length
  simp only [List.length_append,BitstringEncoding.length_delimit,bitstring_list_encoded_length,
    List.length_nil,Nat.mul_zero,Nat.add_zero,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  rw [input_encoded_length,input_encoded_length,hcode]
  simp only [tapeLength] at ht
  omega

def evaluate : Input × List Bool → Input := TM2UnaryIterate.result ReferenceChoiceStep.step

theorem evaluate_isPolyTime : ComplexityTheory.IsPolyTime evaluate := by
  apply TM2UnaryIterate.result_isPolyTime_of_prefix_bound ReferenceChoiceStep.step step_isPolyTime
  exact ⟨Polynomial.C 64 * Polynomial.X, prefix_encoded_bound⟩

def accepts (p : Input × List Bool) : Bool := zero (base (evaluate p))

theorem accepts_isPolyTime : ComplexityTheory.IsPolyTime accepts := by
  have hb : ComplexityTheory.IsPolyTime (fun p : Input × List Bool => base (evaluate p)) :=
    TM2Compose.isPolyTime_comp evaluate base evaluate_isPolyTime TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime (fun p : Input × List Bool => state (base (evaluate p))) :=
    TM2Compose.isPolyTime_comp (fun p : Input × List Bool => base (evaluate p)) state hb TM2GuardAllStep.second_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Input × List Bool => state (base (evaluate p)))
    Source284RecordBitCost.isZero hs Source284ZeroTM2.isZero_isPolyTime

/-- This paid evaluator preserves the source's exact clock and accepts on the
final allowed HALT step; a timeout is false. -/
theorem accepts_correct (p : Input) (clock : List Bool) (h : (numericConfig p).state ≠ 0) :
    accepts (p,clock) = true ↔
      Source.haltedWithin (Shared.Codes.BitNumeralCompare.value (code (base p))) clock.length
        (toSim (numericConfig p) (Shared.Codes.BitNumeralCompare.value (choices p))) = true := by
  change Source284RecordBitCost.isZero
    (state (base (TM2UnaryIterate.run ReferenceChoiceStep.step p clock.length))) = true ↔ _
  rw [Source284RecordBitCost.isZero_correct]
  exact (ReferenceChoiceStep.run_matches p clock.length h).symm

end Shared.PNP.Record285.ReferenceChoiceGrowth
