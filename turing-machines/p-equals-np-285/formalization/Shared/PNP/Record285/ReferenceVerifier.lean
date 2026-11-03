import Shared.PNP.Record285.ReferenceChoiceGrowth
import Shared.PNP.Record285.CandidateCanonicalParsing
import Shared.PNP.Record285.WitnessTruncation

/-! Paid all-bitstrings parsing and witness wrapper for the exact 285
source reference language. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace Shared.PNP.Record285.ReferenceVerifier
open Shared.ComplexityBridge
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.CandidateCanonicalParsing
open Shared.PNP.Record285.CandidateCanonicalSimulation
open Shared.PNP.Record285.ReferenceRecordWorker
open Shared.PNP.Record285.MaskedFramePoly (constBoolList)

abbrev Bits := List Bool

def payloadAt (p : Bits × Nat) : Bool :=
  TM2InputBitLookup.lookup (p.1,halfLength p.1 + 1 + p.2)

theorem payloadAt_isPolyTime : ComplexityTheory.IsPolyTime payloadAt := by
  let input : Bits × Nat → Bits := fun p => p.1
  let index : Bits × Nat → Nat := fun p => p.2
  let half : Bits × Nat → Nat := fun p => halfLength p.1
  have hi : ComplexityTheory.IsPolyTime input := TM2PairFirst.first_isPolyTime
  have hj : ComplexityTheory.IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have hh : ComplexityTheory.IsPolyTime half := TM2Compose.isPolyTime_comp input halfLength hi halfLength_isPolyTime
  have ho : ComplexityTheory.IsPolyTime (fun p : Bits × Nat => half p + 1) := add half (fun _ => 1) hh (constNat 1)
  have hs : ComplexityTheory.IsPolyTime (fun p : Bits × Nat => half p + 1 + index p) :=
    add (fun p => half p + 1) index ho hj
  have hp := TM2GuardAllStep.pair_isPolyTime input (fun p : Bits × Nat => half p + 1 + index p) hi hs
  exact TM2Compose.isPolyTime_comp (fun p => (input p,half p + 1 + index p))
    TM2InputBitLookup.lookup hp TM2InputBitLookup.lookup_isPolyTime

def payloadBits (input : Bits) : Bits :=
  TM2ContextMapGeneric.contextMap payloadAt (input,TM2UnaryRange.rangeFromTokens (halfTokens input))

theorem payloadBits_isPolyTime : ComplexityTheory.IsPolyTime payloadBits := by
  let indices : Bits → List Nat := fun input => TM2UnaryRange.rangeFromTokens (halfTokens input)
  have hi : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp halfTokens
    TM2UnaryRange.rangeFromTokens halfTokens_isPolyTime TM2UnaryRange.rangeFromTokens_isPolyTime
  have hid : ComplexityTheory.IsPolyTime (id : Bits → Bits) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hp := TM2GuardAllStep.pair_isPolyTime (id : Bits → Bits) indices hid hi
  exact TM2Compose.isPolyTime_comp (fun input => (input,indices input))
    (TM2ContextMapGeneric.contextMap payloadAt) hp
    (TM2ContextMapGeneric.contextMap_isPolyTime payloadAt payloadAt_isPolyTime)

theorem payloadBits_canonical (payload : Bits) : payloadBits (canonical payload) = payload := by
  have hhalf : halfLength (canonical payload) = payload.length := by
    simp only [halfLength,Nat.div2_val,canonical_length]
    omega
  have htokens : (halfTokens (canonical payload)).length = payload.length := by
    rw [halfTokens_length,canonical_length]
    omega
  unfold payloadBits TM2ContextMapGeneric.contextMap TM2UnaryRange.rangeFromTokens
  rw [htokens]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < payload.length := by simpa using hj
    simp only [List.getElem_map,List.getElem_range,payloadAt,TM2InputBitLookup.lookup_correct,hhalf]
    rw [canonical_bit]
    simp only [show ¬payload.length+1+i < payload.length by omega,
      show payload.length+1+i ≠ payload.length by omega,if_false]
    have he : payload.length+1+i-(payload.length+1) = i := by omega
    rw [he,List.getElem?_eq_getElem hi']
    rfl

def programBits (input : Bits) : Bits := payloadBits input ++ [true]

theorem programBits_isPolyTime : ComplexityTheory.IsPolyTime programBits := by
  have hp := TM2GuardAllStep.pair_isPolyTime payloadBits (fun _ : Bits => [true])
    payloadBits_isPolyTime (constBoolList [true])
  exact TM2Compose.isPolyTime_comp (fun input : Bits => (payloadBits input,[true]))
    (TM2ListAppend.append (α := Bool)) hp TM2ListAppend.append_isPolyTime

/-- Both tape halves start blank, state one is live, and the witness provides
the source's low-bit-first nondeterministic choices. -/
def initial (p : Bits × Bits) : ReferenceChoiceStep.Input :=
  (((programBits p.1,([],[])),[true]),p.2)

theorem initial_isPolyTime : ComplexityTheory.IsPolyTime initial := by
  let input : Bits × Bits → Bits := fun p => p.1
  let witness : Bits × Bits → Bits := fun p => p.2
  let code : Bits × Bits → Bits := fun p => programBits p.1
  let empty : Bits × Bits → Bits := fun _ => []
  let one : Bits × Bits → Bits := fun _ => [true]
  have hi : ComplexityTheory.IsPolyTime input := TM2PairFirst.first_isPolyTime
  have hw : ComplexityTheory.IsPolyTime witness := TM2GuardAllStep.second_isPolyTime
  have hc : ComplexityTheory.IsPolyTime code := TM2Compose.isPolyTime_comp input programBits hi programBits_isPolyTime
  have he : ComplexityTheory.IsPolyTime empty := TM2EmptyConstant.isPolyTime [] rfl
  have ho : ComplexityTheory.IsPolyTime one := constBoolList [true]
  have ht := TM2GuardAllStep.pair_isPolyTime empty empty he he
  have hctx := TM2GuardAllStep.pair_isPolyTime code (fun p => (empty p,empty p)) hc ht
  have hb := TM2GuardAllStep.pair_isPolyTime (fun p => (code p,(empty p,empty p))) one hctx ho
  exact TM2GuardAllStep.pair_isPolyTime (fun p => ((code p,(empty p,empty p)),one p)) witness hb hw

def clock (p : Bits × Bits) : Bits := halfTokens p.1

def valid (p : Bits × Bits) : Bool := validFrame p.1

def verifier (p : Bits × Bits) : Bool :=
  if valid p then ReferenceChoiceGrowth.accepts (initial p,clock p) else false

theorem verifier_isPolyTime : ComplexityTheory.IsPolyTime verifier := by
  have hi : ComplexityTheory.IsPolyTime (fun p : Bits × Bits => p.1) := TM2PairFirst.first_isPolyTime
  have hc : ComplexityTheory.IsPolyTime clock :=
    TM2Compose.isPolyTime_comp (fun p : Bits × Bits => p.1) halfTokens hi halfTokens_isPolyTime
  have hv : ComplexityTheory.IsPolyTime valid :=
    TM2Compose.isPolyTime_comp (fun p : Bits × Bits => p.1) validFrame hi validFrame_isPolyTime
  have hp := TM2GuardAllStep.pair_isPolyTime initial clock initial_isPolyTime hc
  have ha : ComplexityTheory.IsPolyTime (fun p : Bits × Bits => ReferenceChoiceGrowth.accepts (initial p,clock p)) :=
    TM2Compose.isPolyTime_comp (fun p => (initial p,clock p)) ReferenceChoiceGrowth.accepts hp ReferenceChoiceGrowth.accepts_isPolyTime
  exact TM2If.if_isPolyTime valid (fun p => ReferenceChoiceGrowth.accepts (initial p,clock p))
    (fun _ => false) hv ha (TM2Constant.isPolyTime false)

theorem verifier_canonical (payload witness : Bits) :
    verifier (canonical payload,witness) = true ↔
      Source.haltedWithin (2^payload.length + value payload) payload.length
        ⟨0,0,0,value witness⟩ = true := by
  have hv : valid (canonical payload,witness) = true :=
    (validFrame_correct (canonical payload)).2 ⟨payload,rfl⟩
  have hn : (ReferenceChoiceStep.numericConfig (initial (canonical payload,witness))).state ≠ 0 := by
    simp [initial,ReferenceChoiceStep.numericConfig,ReferenceChoiceStep.base,
      Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep.config,
      Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep.state,
      Shared.Beeping.NPcoNP.Source284EvaluatorBitStep.denote,
      Shared.Codes.BitNumeralCompare.value]
  have h := ReferenceChoiceGrowth.accepts_correct
    (initial (canonical payload,witness)) (clock (canonical payload,witness)) hn
  simp only [verifier,hv,if_true]
  convert h using 1 <;>
    simp [initial,clock,ReferenceChoiceStep.numericConfig,ReferenceChoiceStep.base,
      ReferenceChoiceStep.choices,ReferenceChoiceStep.toSim,
      Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep.code,
      Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep.config,
      Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep.left,
      Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep.right,
      Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep.state,
      Shared.Beeping.NPcoNP.Source284EvaluatorBitStep.denote,
      values_agree,programBits,payloadBits_canonical,
      HardwireChoiceLoader.value_append,CanonicalInput.value,Nat.add_comm]

/-- All witness suffixes are allowed: only the first `n` choices can be
observed in `n` steps, so even a longer witness denotes a searched branch. -/
theorem verifier_sound_canonical (payload witness : Bits)
    (h : verifier (canonical payload,witness) = true) :
    referenceLanguage (canonical payload) = true := by
  have hh := (verifier_canonical payload witness).1 h
  have htr := WitnessTruncation.haltedWithin_truncate
    (2^payload.length+value payload) payload.length ⟨0,0,0,value witness⟩
  have hh' : Source.haltedWithin (2^payload.length+value payload) payload.length
      ⟨0,0,0,value witness % 2^payload.length⟩ = true := by
    simpa using htr ▸ hh
  have hb : value witness % 2^payload.length < 2^payload.length :=
    Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))
  have hs := (Source.referenceSearch_spec (2^payload.length+value payload) payload.length (2^payload.length)).2
    ⟨value witness % 2^payload.length,hb,hh'⟩
  simpa [referenceLanguage,Source.reference] using hs

/-- A searched branch is represented by exactly `n` low-bit-first choice
bits; its verifier witness is no longer than the payload. -/
theorem verifier_complete_canonical (payload : Bits)
    (h : referenceLanguage (canonical payload) = true) :
    ∃ witness, witness.length ≤ payload.length ∧ verifier (canonical payload,witness) = true := by
  have hs : Source.referenceSearch (2^payload.length+value payload) payload.length (2^payload.length) = true := by
    simpa [referenceLanguage,Source.reference] using h
  obtain ⟨branch,hbranch,haccept⟩ := (Source.referenceSearch_spec _ _ _).1 hs
  refine ⟨bits payload.length branch, by simp, ?_⟩
  apply (verifier_canonical payload _).2
  simpa [value_bits_of_lt _ _ hbranch] using haccept

/-- The actual bounded-source reference belongs to the pinned canonical NP,
with malformed bitstrings rejected and a linear-size Boolean-list witness. -/
theorem reference_in_NP : referenceLanguage ∈ ComplexityTheory.NP := by
  refine ⟨Polynomial.X,verifier,verifier_isPolyTime,?_⟩
  intro input
  change referenceLanguage input = true ↔
    ∃ witness, witness.length ≤ Polynomial.X.eval input.length ∧ verifier (input,witness) = true
  by_cases hv : validFrame input = true
  · obtain ⟨payload,rfl⟩ := (validFrame_correct input).1 hv
    constructor
    · intro h
      obtain ⟨w,hw,ha⟩ := verifier_complete_canonical payload h
      refine ⟨w,?_,ha⟩
      simp only [Polynomial.eval_X,canonical_length]
      omega
    · rintro ⟨w,_,ha⟩
      exact verifier_sound_canonical payload w ha
  · have hv' : validFrame input = false := by cases h : validFrame input <;> simp_all
    have hp : CanonicalInput.parse input = none := by
      cases hx : CanonicalInput.parse input with
      | none => rfl
      | some payload =>
        have ht : validFrame input = true := (validFrame_correct input).2 ⟨payload,CanonicalInput.parse_sound hx⟩
        contradiction
    simp [referenceLanguage,hp,verifier,valid,hv']

/-- The exact bounded source language has a polynomial-time decider exactly
when the pinned canonical classes coincide. -/
theorem reference_P_iff_P_eq_NP :
    ComplexityTheory.IsPolyTime referenceLanguage ↔ ComplexityTheory.P = ComplexityTheory.NP := by
  constructor
  · exact MaskedFramePoly.reference_in_P_implies_P_eq_NP
  · intro h
    change referenceLanguage ∈ ComplexityTheory.P
    rw [h]
    exact reference_in_NP

/-- Only the explicit uniform paid frame wrapper remains on the complexity
side of this conditional literal-machine equivalence. -/
theorem literal_silent_iff_P_eq_NP_of_wrapper
    (hwrap : CanonicalPBridge.FrameEncodingWrapper) :
    Shared.PNP.Record285.machine.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  CandidateCanonicalParsing.literal_silent_iff_P_eq_NP_of_membership_and_wrapper reference_in_NP hwrap

theorem literal_finiteEvents_iff_P_eq_NP_of_wrapper
    (hwrap : CanonicalPBridge.FrameEncodingWrapper) :
    Shared.PNP.Record285.machine.system.FiniteEventTimes ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  Shared.PNP.Record285.machine.system.eventuallySilent_iff_finiteEventTimes.symm.trans
    (literal_silent_iff_P_eq_NP_of_wrapper hwrap)

theorem literal_infinitelyMany_iff_P_ne_NP_of_wrapper
    (hwrap : CanonicalPBridge.FrameEncodingWrapper) :
    Shared.PNP.Record285.machine.system.InfinitelyManyBeeps ↔ ComplexityTheory.P ≠ ComplexityTheory.NP := by
  rw [← Shared.Beeping.EventSystem.not_eventuallySilent_iff_infinitelyMany]
  exact not_congr (literal_silent_iff_P_eq_NP_of_wrapper hwrap)

end Shared.PNP.Record285.ReferenceVerifier
