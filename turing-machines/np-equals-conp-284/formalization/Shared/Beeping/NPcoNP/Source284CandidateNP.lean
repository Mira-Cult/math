import Shared.Beeping.NPcoNP.Source284CandidateClock
import Shared.Beeping.NPcoNP.Source284CandidateWitness
import Shared.Beeping.NPcoNP.Source284EvaluatorAccept
import Shared.Beeping.NPcoNP.Source284FixedTableReduction
import Shared.ComplexityBridge.TM2UnaryLengthCheck
import Shared.ComplexityBridge.TM2If

/-! Canonical NP membership for each fixed candidate of the selected 284
source. The candidate number is fixed in the finite checker, and is used
both as the source program and clock exponent. The original witness cutoff
is checked before evaluation, and the whole input is supplied to the source
program. This is not candidate coverage or a physical-machine refinement. -/

namespace Shared.Beeping.NPcoNP.Source284CandidateNP

open ComplexityTheory Shared.ComplexityBridge
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep

abbrev Input := List Bool × List Bool

def clock (j : Nat) (p : Input) : List Bool := Source284CandidateClock.clock j p.1
def initial (j : Nat) (p : Input) : Packed := ((j.bits,(p.2,p.1)),[true])
def request (j : Nat) (p : Input) : Packed × List Bool := (initial j p,clock j p)
def within (j : Nat) (p : Input) : Bool := TM2UnaryLengthCheck.fits (clock j p,p.2)
def checker (j : Nat) (p : Input) : Bool :=
  if within j p then Source284EvaluatorAccept.accepts (request j p) else false

/-- The machine may depend on `j`, but no tested input controls its fixed
description or exponent. -/
theorem checker_isPolyTime (j : Nat) : IsPolyTime (checker j) := by
  let first : Input → List Bool := fun p => p.1
  let witness : Input → List Bool := fun p => p.2
  let program : Input → List Bool := fun _ => j.bits
  have hfirst : IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hwitness : IsPolyTime witness := TM2GuardAllStep.second_isPolyTime
  have hprogram : IsPolyTime program := by
    have h := TM2Compose.isPolyTime_comp first (fun _ : List Bool => j.bits) hfirst
      (Source284FixedTableReduction.constList_isPolyTime j.bits)
    simpa [program, first] using h
  have hclock : IsPolyTime (clock j) := by
    exact TM2Compose.isPolyTime_comp first (Source284CandidateClock.clock j) hfirst
      (Source284CandidateClock.clock_isPolyTime j)
  have htrue : IsPolyTime (fun _ : Input => true) := TM2Constant.isPolyTime true
  have hone : IsPolyTime (fun _ : Input => [true]) :=
    TM2GateCNFPieces.singleton_isPolyTime (fun _ : Input => true) htrue
  have htapes : IsPolyTime (fun p : Input => (witness p, first p)) :=
    TM2GuardAllStep.pair_isPolyTime witness first hwitness hfirst
  have hctx : IsPolyTime (fun p : Input => (program p,(witness p,first p))) :=
    TM2GuardAllStep.pair_isPolyTime program (fun p => (witness p,first p)) hprogram htapes
  have hinit : IsPolyTime (initial j) := by
    change IsPolyTime (fun p : Input => ((j.bits,(p.2,p.1)),[true]))
    simpa [program, witness, first] using
      (TM2GuardAllStep.pair_isPolyTime (fun p : Input => (program p,(witness p,first p)))
        (fun _ => [true]) hctx hone)
  have hrequest : IsPolyTime (request j) :=
    TM2GuardAllStep.pair_isPolyTime (initial j) (clock j) hinit hclock
  have hbody : IsPolyTime (fun p : Input => Source284EvaluatorAccept.accepts (request j p)) :=
    TM2Compose.isPolyTime_comp (request j) Source284EvaluatorAccept.accepts hrequest
      Source284EvaluatorAccept.accepts_isPolyTime
  have hguardArgs : IsPolyTime (fun p : Input => (clock j p,witness p)) :=
    TM2GuardAllStep.pair_isPolyTime (clock j) witness hclock hwitness
  have hwithin : IsPolyTime (within j) :=
    TM2Compose.isPolyTime_comp (fun p : Input => (clock j p,witness p))
      TM2UnaryLengthCheck.fits hguardArgs TM2UnaryLengthCheck.fits_isPolyTime
  have hfalse : IsPolyTime (fun _ : Input => false) := TM2Constant.isPolyTime false
  exact TM2If.if_isPolyTime (within j) (fun p => Source284EvaluatorAccept.accepts (request j p))
    (fun _ => false) hwithin hbody hfalse

theorem checker_correct (j : Nat) (xs w : List Bool) :
    checker j (xs,w) =
      if w.length ≤ Source284Comparison.clock j (value xs) then
        Source284Relative.accepts j (value xs) (value w)
          (Source284Comparison.clock j (value xs))
      else false := by
  have hclock := Source284CandidateClock.clock_length j xs
  by_cases h : w.length ≤ Source284Comparison.clock j (value xs)
  · have hf : TM2UnaryLengthCheck.fits (Source284CandidateClock.clock j xs,w) = true :=
      TM2UnaryLengthCheck.fits_correct _ |>.2 (by simpa [hclock] using h)
    simp only [checker,within,clock,hf, ↓reduceIte, h]
    rw [Source284EvaluatorAccept.accepts_correct]
    simp [request,initial,clock, Source284EvaluatorPackedStep.code,
      Source284EvaluatorPackedStep.config, Source284EvaluatorPackedStep.left,
      Source284EvaluatorPackedStep.right, Source284EvaluatorPackedStep.state,
      Source284EvaluatorBitStep.denote, Source284Relative.accepts,
      Source284Relative.initial, Shared.Codes.BinaryAdditionCanonical.value_bits,
      value, hclock]
  · have hf : TM2UnaryLengthCheck.fits (Source284CandidateClock.clock j xs,w) = false := by
      cases hb : TM2UnaryLengthCheck.fits (Source284CandidateClock.clock j xs,w) with
      | false => rfl
      | true =>
        have hh := (TM2UnaryLengthCheck.fits_correct _).1 hb
        rw [hclock] at hh
        exact False.elim (h hh)
    simp [checker,within,clock,hf, h]

/-- Every fixed source candidate defines a language in the pinned canonical
NP class. The outer polynomial bounds the witness length; the checker keeps
the smaller original clock cutoff, so enlarged bounds cannot add witnesses. -/
theorem candidate_mem_NP (j : Nat) : candidateLanguage j ∈ NP := by
  refine ⟨(Polynomial.X + Polynomial.C 1) ^ j, checker j, checker_isPolyTime j, ?_⟩
  intro xs
  simpa [checker_correct] using
    Source284CandidateWitness.candidateLanguage_iff_guarded_witness j xs

theorem all_candidates_mem_NP : ∀ j, candidateLanguage j ∈ NP := candidate_mem_NP

end Shared.Beeping.NPcoNP.Source284CandidateNP
