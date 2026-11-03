import Shared.ComplexityBridge.TM2TripleRepack
import Shared.ComplexityBridge.TM2UnaryRange
import Shared.ComplexityBridge.TM2Serialize

/-! Polynomial-time bit lookup using the existing finite framed-name lookup.
All encoded indices are generated from a range bounded by the input list. -/
namespace Shared.ComplexityBridge.TM2InputBitLookup
open Shared.ComplexityBridge

/-- A total bit lookup; out-of-range indices return false. -/
def lookup (p : List Bool × Nat) : Bool :=
  TM2WitnessComplete.lookupTriple
    (BitstringEncoding.bitEncode (List.range p.1.length),
      (p.1,BitstringEncoding.bitEncode p.2))

theorem assignment_range' (bits : List Bool) (base index : Nat) :
    CNF.assignment (List.range' base bits.length) bits index =
      if index < base then false else (bits[index-base]?).getD false := by
  induction bits generalizing base index with
  | nil => simp [CNF.assignment]
  | cons b bs ih =>
    simp only [List.length_cons,List.range'_succ,CNF.assignment]
    by_cases he : index = base
    · subst index; simp
    · by_cases hl : index < base
      · have hl' : index < base+1 := by omega
        simp [he,hl,ih,hl']
      · have hl' : ¬ index < base+1 := by omega
        have hd : index-base = (index-(base+1))+1 := by omega
        simp [he,hl,ih,hl',hd]

theorem lookup_correct (bits : List Bool) (n : Nat) :
    lookup (bits,n) = (bits[n]?).getD false := by
  let vars : List (List Bool) := (List.range bits.length).map (BitstringEncoding.bitEncode : Nat → List Bool)
  have hf : BitstringEncoding.bitEncode (List.range bits.length) = TM2WitnessLookup.frames vars := by
    rfl
  have hv : vars.map Computability.decodeNat = List.range bits.length := by
    have hdec (x : Nat) : Computability.decodeNat (BitstringEncoding.bitEncode x) = x :=
      Computability.decode_encodeNat x
    simp [vars,List.map_map,Function.comp_def,hdec]
  change TM2WitnessLookup.lookupRaw (BitstringEncoding.bitEncode (List.range bits.length)) bits
    (BitstringEncoding.bitEncode n) = _
  rw [hf,TM2WitnessLookup.lookupRaw_frames,RawCNFLookup.lookup_correct,hv]
  rw [List.range_eq_range']
  change CNF.assignment (List.range' 0 bits.length) bits (Computability.decodeNat (Computability.encodeNat n)) = _
  simp only [Computability.decode_encodeNat]
  simpa using assignment_range' bits 0 n

theorem lookup_isPolyTime : ComplexityTheory.IsPolyTime lookup := by
  let bits : List Bool × Nat → List Bool := fun p => p.1
  let index : List Bool × Nat → Nat := fun p => p.2
  let indices : List Bool × Nat → List Nat := fun p => TM2UnaryRange.rangeFromTokens (bits p)
  let raw : List Bool × Nat → List Bool := fun p => BitstringEncoding.bitEncode (indices p)
  let query : List Bool × Nat → List Bool := fun p => BitstringEncoding.bitEncode (index p)
  let args : List Bool × Nat → TM2WitnessComplete.Triple := fun p => (raw p,(bits p,query p))
  have hb : ComplexityTheory.IsPolyTime bits := TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have hn : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp bits TM2UnaryRange.rangeFromTokens hb TM2UnaryRange.rangeFromTokens_isPolyTime
  have hr : ComplexityTheory.IsPolyTime raw := TM2Compose.isPolyTime_comp indices (BitstringEncoding.bitEncode : List Nat → List Bool) hn TM2Serialize.isPolyTime
  have hq : ComplexityTheory.IsPolyTime query := TM2Compose.isPolyTime_comp index (BitstringEncoding.bitEncode : Nat → List Bool) hi TM2Serialize.isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime raw (fun p => (bits p,query p)) hr
    (TM2GuardAllStep.pair_isPolyTime bits query hb hq)
  have h := TM2Compose.isPolyTime_comp args TM2WitnessComplete.lookupTriple ha TM2TripleRepack.lookupTriple_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : List Bool × Nat => TM2WitnessComplete.lookupTriple
    (BitstringEncoding.bitEncode (List.range p.1.length),(p.1,BitstringEncoding.bitEncode p.2)))
  simpa [args,raw,indices,bits,query,index,TM2UnaryRange.rangeFromTokens] using h

namespace Fixtures
example : lookup ([],0) = false := rfl
example : lookup ([true,false,true],0) = true := rfl
example : lookup ([true,false,true],1) = false := rfl
example : lookup ([true,false,true],3) = false := rfl
end Fixtures
end Shared.ComplexityBridge.TM2InputBitLookup
