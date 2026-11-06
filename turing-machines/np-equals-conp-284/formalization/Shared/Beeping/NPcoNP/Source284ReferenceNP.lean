import Shared.Beeping.NPcoNP.Source284ParserTM2
import Shared.Beeping.NPcoNP.Source284RawWitness
import Shared.Beeping.NPcoNP.Source284EvaluatorAccept
import Shared.ComplexityBridge.TM2UnaryLengthCheck
import Shared.ComplexityBridge.TM2If

/-! Canonical NP membership for the 284 source's reference language.
The checker uses the actual polynomial-time marker parser and bounded
evaluator, retaining the source's original witness cutoff. It is not a
hardness proof or a refinement of the literal beeping machine. -/

namespace Shared.Beeping.NPcoNP.Source284ReferenceNP

open ComplexityTheory Shared.ComplexityBridge
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep

abbrev Input := List Bool × List Bool

def parsed (p : Input) : List Bool × List Bool := Source284ParserTM2.parse p.1
def clock (p : Input) : List Bool := (parsed p).1
def program (p : Input) : List Bool := (parsed p).2
def initial (p : Input) : Packed := ((program p,(p.2,[])),[true])
def request (p : Input) : Packed × List Bool := (initial p,clock p)
def within (p : Input) : Bool := TM2UnaryLengthCheck.fits (clock p,p.2)
def checker (p : Input) : Bool :=
  if within p then Source284EvaluatorAccept.accepts (request p) else false

/-- Every projection, pairing, parser, cutoff check, and evaluator call in
the witness relation has its own canonical polynomial-time implementation. -/
theorem checker_isPolyTime : IsPolyTime checker := by
  let first : Input → List Bool := fun p => p.1
  let witness : Input → List Bool := fun p => p.2
  have hfirst : IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hwitness : IsPolyTime witness := TM2GuardAllStep.second_isPolyTime
  have hparsed : IsPolyTime parsed :=
    TM2Compose.isPolyTime_comp first Source284ParserTM2.parse hfirst
      Source284ParserTM2.parse_isPolyTime
  have hclock : IsPolyTime clock :=
    TM2Compose.isPolyTime_comp parsed (fun p : List Bool × List Bool => p.1)
      hparsed TM2PairFirst.first_isPolyTime
  have hprogram : IsPolyTime program :=
    TM2Compose.isPolyTime_comp parsed (fun p : List Bool × List Bool => p.2)
      hparsed TM2GuardAllStep.second_isPolyTime
  have hempty : IsPolyTime (fun _ : Input => ([] : List Bool)) :=
    TM2EmptyConstant.isPolyTime [] rfl
  have htrue : IsPolyTime (fun _ : Input => true) := TM2Constant.isPolyTime true
  have hone : IsPolyTime (fun _ : Input => [true]) :=
    TM2GateCNFPieces.singleton_isPolyTime (fun _ : Input => true) htrue
  have htapes : IsPolyTime (fun p : Input => (witness p, ([] : List Bool))) :=
    TM2GuardAllStep.pair_isPolyTime witness (fun _ => []) hwitness hempty
  have hctx : IsPolyTime (fun p : Input => (program p,(witness p,([] : List Bool)))) :=
    TM2GuardAllStep.pair_isPolyTime program (fun p => (witness p,[])) hprogram htapes
  have hinit : IsPolyTime initial := by
    change IsPolyTime (fun p : Input => ((program p,(p.2,([] : List Bool))),[true]))
    simpa [witness] using
      (TM2GuardAllStep.pair_isPolyTime (fun p : Input => (program p,(witness p,([] : List Bool))))
        (fun _ => [true]) hctx hone)
  have hrequest : IsPolyTime request := TM2GuardAllStep.pair_isPolyTime initial clock hinit hclock
  have hbody : IsPolyTime (fun p : Input => Source284EvaluatorAccept.accepts (request p)) :=
    TM2Compose.isPolyTime_comp request Source284EvaluatorAccept.accepts hrequest
      Source284EvaluatorAccept.accepts_isPolyTime
  have hguardArgs : IsPolyTime (fun p : Input => (clock p,witness p)) :=
    TM2GuardAllStep.pair_isPolyTime clock witness hclock hwitness
  have hwithin : IsPolyTime within :=
    TM2Compose.isPolyTime_comp (fun p : Input => (clock p,witness p))
      TM2UnaryLengthCheck.fits hguardArgs TM2UnaryLengthCheck.fits_isPolyTime
  have hfalse : IsPolyTime (fun _ : Input => false) := TM2Constant.isPolyTime false
  exact TM2If.if_isPolyTime within (fun p => Source284EvaluatorAccept.accepts (request p))
    (fun _ => false) hwithin hbody hfalse

/-- The concrete TM2 checker implements the independently defined source
relation, including timeout rejection and the original witness cutoff. -/
theorem checker_correct (xs w : List Bool) :
    checker (xs,w) = Source284RawWitness.checker (xs,w) := by
  have hclock := Source284ParserTM2.clock_length xs
  have hprogram := Source284ParserTM2.description_value xs
  by_cases h : w.length ≤ Source284Parser.length (value xs)
  · have hf : TM2UnaryLengthCheck.fits ((Source284ParserTM2.parse xs).1,w) = true :=
      TM2UnaryLengthCheck.fits_correct _ |>.2 (by simpa [hclock] using h)
    simp only [checker,within,clock,parsed,hf, ↓reduceIte,
      Source284RawWitness.checker, h]
    rw [Source284EvaluatorAccept.accepts_correct]
    simp [request,initial,program,clock,parsed,
      Source284EvaluatorPackedStep.code, Source284EvaluatorPackedStep.config,
      Source284EvaluatorPackedStep.left, Source284EvaluatorPackedStep.right,
      Source284EvaluatorPackedStep.state, Source284EvaluatorBitStep.denote,
      Source284Relative.accepts, Source284Relative.initial, value, hclock, hprogram]
  · have hf : TM2UnaryLengthCheck.fits ((Source284ParserTM2.parse xs).1,w) = false := by
      cases hb : TM2UnaryLengthCheck.fits ((Source284ParserTM2.parse xs).1,w) with
      | false => rfl
      | true =>
        have hh := (TM2UnaryLengthCheck.fits_correct _).1 hb
        rw [hclock] at hh
        exact False.elim (h hh)
    simp [checker,within,clock,parsed,hf, Source284RawWitness.checker, h]

/-- The selected source reference belongs to the public library's actual
NP class. Witnesses are raw Boolean lists bounded by the polynomial X. -/
theorem reference_mem_NP : referenceLanguage ∈ NP := by
  refine ⟨Polynomial.X, checker, checker_isPolyTime, ?_⟩
  intro xs
  simpa [checker_correct] using Source284RawWitness.reference_witness xs

end Shared.Beeping.NPcoNP.Source284ReferenceNP
