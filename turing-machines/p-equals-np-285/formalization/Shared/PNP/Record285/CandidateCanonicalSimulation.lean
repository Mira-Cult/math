import Shared.PNP.Record285.Candidate284Adapter
import Shared.PNP.Record285.MaskedFramePoly
import Shared.Codes.BinaryAdditionCanonical

/-! Charged simulation of a fixed 285-source candidate on canonical frames.
The input checker below is only claimed to agree on well-formed frames; that
is sufficient for the explicitly constructed SAT reduction. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Shared.PNP.Record285.CandidateCanonicalSimulation
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.FiniteProgramAdapter (canonical_value)
open Shared.PNP.Record285.Candidate284Adapter
open Shared.PNP.Record285.MaskedFramePoly
open Shared.PNP.Record285.FramedVerifier
open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP

/-- The source clock depends on half of the complete frame length. For a
canonical `1^n 0 payload` frame this is exactly the original payload length. -/
def halfTokens (input : List Bool) : List Bool :=
  TM2BoundedUnary.expand (input,input.length.div2)

theorem halfTokens_isPolyTime : ComplexityTheory.IsPolyTime halfTokens := by
  have hi : ComplexityTheory.IsPolyTime (fun input : List Bool => input) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hl := TM2BinaryListLength.length_isPolyTime (α := Bool)
  have hd := TM2Compose.isPolyTime_comp (List.length : List Bool → Nat) Nat.div2 hl TM2BinaryHalf.div2_isPolyTime
  have hp := TM2GuardAllStep.pair_isPolyTime (fun input : List Bool => input) (fun input => input.length.div2) hi hd
  exact TM2Compose.isPolyTime_comp (fun input : List Bool => (input,input.length.div2))
    TM2BoundedUnary.expand hp TM2BoundedUnary.expand_isPolyTime

@[simp] theorem halfTokens_length (input : List Bool) : (halfTokens input).length = input.length/2 := by
  simp [halfTokens,TM2BoundedUnary.expand_correct,Nat.div2_val]
  omega

def clockPolynomial (exponent : Nat) : Polynomial Nat := (Polynomial.X+Polynomial.C 2)^exponent

def clockTokens (exponent : Nat) (input : List Bool) : List Bool :=
  TM2UnaryPolynomialIO.unaryPolynomial (clockPolynomial exponent) (halfTokens input)

theorem clockTokens_isPolyTime (exponent : Nat) : ComplexityTheory.IsPolyTime (clockTokens exponent) :=
  TM2Compose.isPolyTime_comp halfTokens (TM2UnaryPolynomialIO.unaryPolynomial (clockPolynomial exponent))
    halfTokens_isPolyTime (TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime _)

@[simp] theorem clockTokens_length (exponent : Nat) (input : List Bool) :
    (clockTokens exponent input).length = (input.length/2+2)^exponent := by
  simp [clockTokens,TM2UnaryPolynomialIO.unaryPolynomial,clockPolynomial,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X]

/-- The fixed auxiliary 284 code and initial state are finite constants; the
complete raw frame remains the actual right tape. -/
def packed (program bits : Nat) (input : List Bool) : Source284EvaluatorPackedStep.Packed :=
  (((encode program bits).bits,([],input)),[true,true])

theorem packed_isPolyTime (program bits : Nat) : ComplexityTheory.IsPolyTime (packed program bits) := by
  let code : List Bool → List Bool := fun _ => (encode program bits).bits
  let empty : List Bool → List Bool := fun _ => []
  let state : List Bool → List Bool := fun _ => [true,true]
  let right : List Bool → List Bool := id
  have hc : ComplexityTheory.IsPolyTime code := constBoolList _
  have he : ComplexityTheory.IsPolyTime empty := TM2EmptyConstant.isPolyTime [] rfl
  have hs : ComplexityTheory.IsPolyTime state := constBoolList _
  have hr : ComplexityTheory.IsPolyTime right := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hp := TM2GuardAllStep.pair_isPolyTime code (fun x => (empty x,right x)) hc
    (TM2GuardAllStep.pair_isPolyTime empty right he hr)
  exact TM2GuardAllStep.pair_isPolyTime (fun x => (code x,(empty x,right x))) state hp hs

def check (program bits exponent : Nat) (input : List Bool) : Bool :=
  Source284EvaluatorAccept.accepts (packed program bits input,clockTokens exponent input)

theorem check_isPolyTime (program bits exponent : Nat) : ComplexityTheory.IsPolyTime (check program bits exponent) := by
  have hp := TM2GuardAllStep.pair_isPolyTime (packed program bits) (clockTokens exponent)
    (packed_isPolyTime program bits) (clockTokens_isPolyTime exponent)
  exact TM2Compose.isPolyTime_comp (fun x => (packed program bits x,clockTokens exponent x))
    Source284EvaluatorAccept.accepts hp Source284EvaluatorAccept.accepts_isPolyTime

theorem values_agree (xs : List Bool) : Shared.Codes.BitNumeralCompare.value xs = value xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [Shared.Codes.BitNumeralCompare.value,value,ih,Nat.add_comm]

/-- The polynomial machine simulates the fixed recoded candidate on every
finite tape word and uses precisely the displayed source clock. -/
theorem check_correct (program bits exponent : Nat) (input : List Bool) :
    check program bits exponent input =
      ((Source284Relative.run (encode program bits)
        ⟨0,value input,Source284TableEncode.active 1⟩ ((input.length/2+2)^exponent)).state == 0) := by
  rw [check,Source284EvaluatorAccept.accepts_correct,clockTokens_length]
  have hcode : value (encode program bits).bits = encode program bits := by
    rw [←values_agree]
    exact Shared.Codes.BinaryAdditionCanonical.value_bits _
  simp [packed,Source284EvaluatorPackedStep.code,Source284EvaluatorPackedStep.config,
    Source284EvaluatorPackedStep.left,Source284EvaluatorPackedStep.right,Source284EvaluatorPackedStep.state,
    Source284EvaluatorBitStep.denote,Source284TableEncode.active,values_agree,hcode,value]

/-- On every admissible frame, the canonical machine returns the exact
source candidate result, including timeout and final-clock HALT. -/
theorem check_canonical (program bits exponent : Nat) (hprogram : program < 2^bits)
    (payload : List Bool) :
    check program bits exponent (canonical payload) = candidateLanguage program exponent (canonical payload) := by
  rw [check_correct]
  have hcandidate := candidate_iff_source284 program bits hprogram exponent payload.length
    (2^payload.length) (value payload)
  have hframe : value (canonical payload) = frame (2^payload.length) (value payload) := canonical_value payload
  have hlen : (canonical payload).length/2 = payload.length := by simp; omega
  rw [hframe,hlen]
  simp only [candidateLanguage,parse_canonical]
  cases hc : candidate program exponent payload.length (2^payload.length) (value payload) <;>
    cases hr : (Source284Relative.run (encode program bits)
      ⟨0,frame (2^payload.length) (value payload),Source284TableEncode.active 1⟩
      ((payload.length+2)^exponent)).state == 0 <;> simp_all

/-- Every aligned SAT reduction output is an actual canonical source frame. -/
theorem alignedFrame_canonical (p : Shared.Codes.FinitePrograms.Program) (time : Polynomial Nat)
    (input : List Bool) : ∃ payload, alignedFrame p time input = canonical payload := by
  unfold alignedFrame FramedVerifier.frame
  exact ⟨_,rfl⟩

/-- One direction of the requested literal endpoint: if the selected
285-state blank-start machine has only finitely many marked transitions,
then canonical P = NP. The argument does not assume either class equality. -/
theorem literal_silent_implies_P_eq_NP
    (hsilent : Shared.PNP.Record285.machine.system.EventuallySilent) :
    ComplexityTheory.P = ComplexityTheory.NP := by
  obtain ⟨program,exponent,hpos,hgood⟩ :=
    Shared.PNP.Record285.SourceControllerSimulation.literal_eventuallySilent_iff_goodCandidate.1 hsilent
  obtain ⟨p,time,hprogram,_⟩ := aligned_sat_compiler_exists
  let reduction : List Bool → List Bool := fun x => alignedFrame p time (CircuitPairWitness.pairPrefix x)
  have hred : ComplexityTheory.IsPolyTime reduction :=
    TM2Compose.isPolyTime_comp CircuitPairWitness.pairPrefix (alignedFrame p time)
      GeneratorFamilyBridge.pairPrefix_isPolyTime (alignedFrame_isPolyTime p time)
  let bits := program+1
  have hb : program < 2^bits := by
    have ha : program < 2^program := Nat.lt_two_pow_self
    have hp : 2^program ≤ 2^(program+1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    exact Nat.lt_of_lt_of_le ha hp
  let decider : List Bool → Bool := fun x => check program bits exponent (reduction x)
  have hd : ComplexityTheory.IsPolyTime decider := TM2Compose.isPolyTime_comp reduction
    (check program bits exponent) hred (check_isPolyTime program bits exponent)
  have he : decider = Shared.ComplexityBridge.CNF.sat := by
    funext x
    have hsat : Shared.ComplexityBridge.CNF.sat x = referenceLanguage (reduction x) := by
      apply Bool.eq_iff_iff.mpr
      exact aligned_sat_correct p time hprogram x
    have hg := (goodCandidate_iff_all_bitstrings program exponent).1 hgood (reduction x)
    obtain ⟨payload,hframe⟩ := alignedFrame_canonical p time (CircuitPairWitness.pairPrefix x)
    have hc : check program bits exponent (reduction x) = candidateLanguage program exponent (reduction x) := by
      change check program bits exponent (alignedFrame p time (CircuitPairWitness.pairPrefix x)) =
        candidateLanguage program exponent (alignedFrame p time (CircuitPairWitness.pairPrefix x))
      rw [hframe]
      exact check_canonical program bits exponent hb payload
    exact hc.trans (hg.trans hsat.symm)
  rw [he] at hd
  exact (CanonicalClasses.p_eq_np_iff_complete_in_p GeneratorGateListClosed.satComplete
    TM2IgnoreWitness.P_subset_NP TM2Compose.p_pullback_closed).2 hd

/-- The requested finite-event polarity for the literal transition table. -/
theorem literal_finiteEvents_implies_P_eq_NP
    (hfinite : Shared.PNP.Record285.machine.system.FiniteEventTimes) :
    ComplexityTheory.P = ComplexityTheory.NP :=
  literal_silent_implies_P_eq_NP
    (Shared.PNP.Record285.machine.system.eventuallySilent_iff_finiteEventTimes.2 hfinite)

/-- Contrapositive in the beeper's intended polarity. -/
theorem literal_infinitelyMany_of_P_ne_NP (hne : ComplexityTheory.P ≠ ComplexityTheory.NP) :
    Shared.PNP.Record285.machine.system.InfinitelyManyBeeps := by
  have hnot : ¬ Shared.PNP.Record285.machine.system.EventuallySilent :=
    fun h => hne (literal_silent_implies_P_eq_NP h)
  exact (Shared.Beeping.EventSystem.not_eventuallySilent_iff_infinitelyMany _).1 hnot

end Shared.PNP.Record285.CandidateCanonicalSimulation
