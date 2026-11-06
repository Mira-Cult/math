import Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep
import Shared.Beeping.NPcoNP.Source284EvaluatorBitGrowth
import Shared.ComplexityBridge.TM2UnaryIterate

/-! The source's bounded relative evaluator iterated for a unary Boolean-list
clock. Program, initial state, and both tape halves are explicit finite input.
This supplies the bounded simulation loop, not the parser/witness wrapper,
canonical NP membership, or a physical beeping-machine refinement. -/

namespace Shared.Beeping.NPcoNP.Source284EvaluatorUnary

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EvaluatorBitStep
open Shared.Beeping.NPcoNP.Source284EvaluatorBitGrowth
open Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep
open Shared.Codes.BitNumeralCompare (value)

theorem repack (p : Packed) : packed (code p) (config p) = p := by
  rcases p with ⟨⟨program,⟨l,r⟩⟩,s⟩
  rfl

/-- The generic iteration carries the entire source configuration in its
first component. The separately initialized empty accumulator is not the
source state, which can start nonzero even when the clock is empty. -/
def evaluate : Packed × List Bool → Packed := TM2UnaryIterate.result step

theorem code_run (p : Packed) (n : Nat) :
    code (TM2UnaryIterate.run step p n) = code p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    change code (TM2UnaryIterate.run step (step p) n) = code p
    rw [ih, code_unchanged]

theorem run_as_fold (p : Packed) (clock : List Bool) :
    TM2UnaryIterate.run step p clock.length =
      packed (code p) (TM2PolynomialFold.fold (clockStep (code p)) (config p) clock) := by
  induction clock generalizing p with
  | nil => simpa [TM2UnaryIterate.run, TM2PolynomialFold.fold] using (repack p).symm
  | cons b bs ih =>
    change TM2UnaryIterate.run step (step p) bs.length = _
    rw [ih, code_unchanged, config_step]
    rfl

theorem evaluate_isPolyTime : ComplexityTheory.IsPolyTime evaluate := by
  apply TM2UnaryIterate.result_isPolyTime_of_prefix_bound step step_isPolyTime
  refine ⟨Polynomial.C 8 * Polynomial.X, ?_⟩
  intro init xs pref tail hxs
  rw [TM2UnaryIterate.fold_value, run_as_fold]
  have h := prefix_encoded_bound (code init) (config init) xs pref tail hxs
  rw [repack] at h
  simpa using h

private theorem source_step_commutes (description : Nat) (c : Source284Relative.Config) (n : Nat) :
    Source284Relative.run description (Source284Relative.step description c) n =
      Source284Relative.step description (Source284Relative.run description c n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Source284Relative.run_succ, ih]

/-- Every finite unary-clock run agrees with the independent numerical
evaluator. The statement includes the zero-clock boundary and arbitrary
noncanonical high zeroes in each bit-list input. -/
theorem evaluate_correct (p : Packed) (clock : List Bool) :
    denote (config (evaluate (p,clock))) =
      Source284Relative.run (value (code p)) (denote (config p)) clock.length := by
  change denote (config (TM2UnaryIterate.run step p clock.length)) = _
  generalize clock.length = n
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    change denote (config (TM2UnaryIterate.run step (step p) n)) = _
    rw [ih, code_unchanged, denote_step, source_step_commutes]
    rfl

end Shared.Beeping.NPcoNP.Source284EvaluatorUnary
