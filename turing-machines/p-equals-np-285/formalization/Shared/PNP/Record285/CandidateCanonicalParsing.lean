import Shared.PNP.Record285.CandidateCanonicalSimulation

/-! Polynomial recognition of the source's exact all-bitstring frame format,
including malformed, empty and zero-payload inputs. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace Shared.PNP.Record285.CandidateCanonicalParsing
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.CandidateCanonicalSimulation
open Shared.PNP.Record285.ReferenceRecordWorker
open Shared.ComplexityBridge

def halfLength (input : List Bool) : Nat := input.length.div2

def prefixBits (input : List Bool) : List Bool :=
  TM2ContextMapGeneric.contextMap TM2InputBitLookup.lookup
    (input,TM2UnaryRange.rangeFromTokens (halfTokens input))

def oddLength (input : List Bool) : Bool :=
  equalNat (input.length,2*halfLength input+1)

def middleBit (input : List Bool) : Bool := TM2InputBitLookup.lookup (input,halfLength input)

def validFrame (input : List Bool) : Bool :=
  oddLength input && !middleBit input && (prefixBits input).all id

theorem halfLength_isPolyTime : ComplexityTheory.IsPolyTime halfLength :=
  TM2Compose.isPolyTime_comp (List.length : List Bool → Nat) Nat.div2
    TM2BinaryListLength.length_isPolyTime TM2BinaryHalf.div2_isPolyTime

theorem prefixBits_isPolyTime : ComplexityTheory.IsPolyTime prefixBits := by
  let indices : List Bool → List Nat := fun input => TM2UnaryRange.rangeFromTokens (halfTokens input)
  have hi : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp halfTokens
    TM2UnaryRange.rangeFromTokens halfTokens_isPolyTime TM2UnaryRange.rangeFromTokens_isPolyTime
  have hid : ComplexityTheory.IsPolyTime (fun input : List Bool => input) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hp := TM2GuardAllStep.pair_isPolyTime (fun input : List Bool => input) indices hid hi
  exact TM2Compose.isPolyTime_comp (fun input => (input,indices input))
    (TM2ContextMapGeneric.contextMap TM2InputBitLookup.lookup) hp
    (TM2ContextMapGeneric.contextMap_isPolyTime TM2InputBitLookup.lookup TM2InputBitLookup.lookup_isPolyTime)

theorem oddLength_isPolyTime : ComplexityTheory.IsPolyTime oddLength := by
  let d : List Bool → Nat := fun input => 2*halfLength input+1
  have hd : ComplexityTheory.IsPolyTime d := add (fun input => 2*halfLength input) (fun _ => 1)
    (double halfLength halfLength_isPolyTime) (constNat 1)
  have hp := TM2GuardAllStep.pair_isPolyTime (List.length : List Bool → Nat) d
    TM2BinaryListLength.length_isPolyTime hd
  exact TM2Compose.isPolyTime_comp (fun input => (input.length,d input)) equalNat hp equalNat_isPolyTime

theorem middleBit_isPolyTime : ComplexityTheory.IsPolyTime middleBit := by
  have hid : ComplexityTheory.IsPolyTime (fun input : List Bool => input) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hp := TM2GuardAllStep.pair_isPolyTime (fun input : List Bool => input) halfLength hid halfLength_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun input => (input,halfLength input)) TM2InputBitLookup.lookup
    hp TM2InputBitLookup.lookup_isPolyTime

theorem validFrame_isPolyTime : ComplexityTheory.IsPolyTime validFrame := by
  let neg : List Bool → Bool := fun input => !(middleBit input)
  let all : List Bool → Bool := fun input => (prefixBits input).all id
  let left : List Bool → Bool := fun input => oddLength input && neg input
  have hn : ComplexityTheory.IsPolyTime neg := TM2Compose.isPolyTime_comp middleBit (fun b => !b)
    middleBit_isPolyTime TM2GateDispatch.not_isPolyTime
  have ha : ComplexityTheory.IsPolyTime all := TM2Compose.isPolyTime_comp prefixBits
    (fun xs : List Bool => xs.all id) prefixBits_isPolyTime TM2GateDispatch.all_isPolyTime
  have hl : ComplexityTheory.IsPolyTime left := TM2Compose.isPolyTime_comp
    (fun input => (oddLength input,neg input)) (fun p : Bool × Bool => p.1 && p.2)
    (TM2GuardAllStep.pair_isPolyTime oddLength neg oddLength_isPolyTime hn) TM2GateDispatch.and_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun input => (left input,all input)) (fun p : Bool × Bool => p.1 && p.2)
    (TM2GuardAllStep.pair_isPolyTime left all hl ha) TM2GateDispatch.and_isPolyTime

/-- Exact structural test with no hidden parser or virtual-zero convention. -/
theorem validFrame_correct (input : List Bool) :
    validFrame input = true ↔ ∃ payload, input = canonical payload := by
  let n := input.length/2
  have hpre : (prefixBits input).all id = true ↔ ∀ i < n, (input[i]?).getD false = true := by
    simp [prefixBits,TM2ContextMapGeneric.contextMap,TM2UnaryRange.rangeFromTokens,
      TM2InputBitLookup.lookup_correct,n,List.all_eq_true]
  have hodd : oddLength input = true ↔ input.length = 2*n+1 := by
    simp [oddLength,equalNat_correct,halfLength,Nat.div2_val,n]
  have hmid : middleBit input = false ↔ (input[n]?).getD false = false := by
    simp [middleBit,TM2InputBitLookup.lookup_correct,halfLength,Nat.div2_val,n]
  have hv : validFrame input = true ↔
      input.length = 2*n+1 ∧ (input[n]?).getD false = false ∧
        ∀ i < n, (input[i]?).getD false = true := by
    simp only [validFrame,Bool.and_eq_true,Bool.not_eq_true',hodd,hmid,hpre,and_assoc]
  rw [hv]
  constructor
  · rintro ⟨hlen,hzero,hones⟩
    have hn : n < input.length := by omega
    have hz : input[n] = false := by simpa [List.getElem?_eq_getElem hn] using hzero
    have ht : input.take n = List.replicate n true := by
      apply List.ext_getElem
      · simp [List.length_take,Nat.min_eq_left (by omega : n ≤ input.length)]
      · intro i hi hj
        have hi' : i < n := by simpa [List.length_take,Nat.min_eq_left (by omega : n ≤ input.length)] using hi
        have hi'' : i < input.length := by omega
        have h := hones i hi'
        simpa [List.getElem_take,List.getElem_replicate,List.getElem?_eq_getElem hi''] using h
    let payload := input.drop (n+1)
    have hp : payload.length = n := by simp [payload]; omega
    refine ⟨payload,?_⟩
    unfold canonical
    rw [hp,←ht,←hz,←List.drop_eq_getElem_cons hn]
    exact (List.take_append_drop n input).symm
  · rintro ⟨payload,rfl⟩
    have hn : (canonical payload).length/2 = payload.length := by simp; omega
    change (canonical payload).length = 2*((canonical payload).length/2)+1 ∧
      (canonical payload)[(canonical payload).length/2]?.getD false = false ∧
      ∀ i < (canonical payload).length/2, (canonical payload)[i]?.getD false = true
    rw [hn,canonical_length]
    constructor
    · rfl
    constructor
    · rw [canonical_bit]
      simp
    · intro i hi
      rw [canonical_bit]
      simp [hi]

/-- The complete all-bitstring source candidate rejects malformed frames and
uses the exact-clock polynomial checker on valid frames. -/
theorem candidateLanguage_isPolyTime (program exponent : Nat) :
    ComplexityTheory.IsPolyTime (candidateLanguage program exponent) := by
  let bits := program+1
  have hb : program < 2^bits := by
    have ha : program < 2^program := Nat.lt_two_pow_self
    have hp : 2^program ≤ 2^(program+1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    exact Nat.lt_of_lt_of_le ha hp
  let checker := check program bits exponent
  have h := TM2If.if_isPolyTime validFrame checker (fun _ => false)
    validFrame_isPolyTime (check_isPolyTime program bits exponent) (TM2Constant.isPolyTime false)
  have he : (fun input => if validFrame input then checker input else false) = candidateLanguage program exponent := by
    funext input
    by_cases hv : validFrame input = true
    · obtain ⟨payload,rfl⟩ := (validFrame_correct input).1 hv
      simp only [hv, ↓reduceIte]
      exact check_canonical program bits exponent hb payload
    · have hv' : validFrame input = false := by cases h : validFrame input <;> simp_all
      have hp : Shared.PNP.Record285.CanonicalInput.parse input = none := by
        cases hx : Shared.PNP.Record285.CanonicalInput.parse input with
        | none => rfl
        | some payload =>
          have hf := parse_sound hx
          have ht : validFrame input = true := (validFrame_correct input).2 ⟨payload,hf⟩
          contradiction
      simp [hv',checker,candidateLanguage,hp]
  rw [he] at h
  exact h

/-- A surviving source candidate makes the exact all-bitstrings reference
polynomial-time, with malformed inputs rejected explicitly. -/
theorem reference_isPolyTime_of_good (program exponent : Nat)
    (hgood : Shared.PNP.Record285.Source.GoodCandidate program exponent) :
    ComplexityTheory.IsPolyTime referenceLanguage := by
  have he : candidateLanguage program exponent = referenceLanguage := by
    funext input
    exact (goodCandidate_iff_all_bitstrings program exponent).1 hgood input
  rw [←he]
  exact candidateLanguage_isPolyTime program exponent

/-- The forward literal-event implication has no extra mathematical premise. -/
theorem literal_silent_implies_reference_P
    (h : Shared.PNP.Record285.machine.system.EventuallySilent) :
    ComplexityTheory.IsPolyTime referenceLanguage := by
  obtain ⟨program,exponent,_,hgood⟩ :=
    Shared.PNP.Record285.SourceControllerSimulation.literal_eventuallySilent_iff_goodCandidate.1 h
  exact reference_isPolyTime_of_good program exponent hgood

/-- The converse still requires the explicitly stated paid raw-frame wrapper. -/
theorem literal_silent_iff_reference_P_of_wrapper
    (hwrap : Shared.PNP.Record285.CanonicalPBridge.FrameEncodingWrapper) :
    Shared.PNP.Record285.machine.system.EventuallySilent ↔ ComplexityTheory.IsPolyTime referenceLanguage := by
  constructor
  · exact literal_silent_implies_reference_P
  · intro h
    exact Shared.PNP.Record285.SourceLiteralEndpoint.literal_silent_of_reference_P_and_wrapper h hwrap

/-- This conditional full endpoint exposes the two remaining complexity-side
obligations: reference NP membership and the uniform raw-frame wrapper. -/
theorem literal_silent_iff_P_eq_NP_of_membership_and_wrapper
    (hNP : referenceLanguage ∈ ComplexityTheory.NP)
    (hwrap : Shared.PNP.Record285.CanonicalPBridge.FrameEncodingWrapper) :
    Shared.PNP.Record285.machine.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP := by
  constructor
  · exact literal_silent_implies_P_eq_NP
  · intro h
    apply Shared.PNP.Record285.SourceLiteralEndpoint.literal_silent_of_reference_P_and_wrapper _ hwrap
    change referenceLanguage ∈ ComplexityTheory.P
    rw [h]
    exact hNP

end Shared.PNP.Record285.CandidateCanonicalParsing
