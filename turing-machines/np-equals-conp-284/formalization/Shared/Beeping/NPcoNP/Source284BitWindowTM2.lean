import Shared.Beeping.NPcoNP.Source284CanonicalPairWindow
import Shared.ComplexityBridge.TM2InputBitLookup
import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.TM2UnaryRange

/-! A canonical polynomial-time bit-window extractor. The window length is
supplied by a unary list; bit-list input is charged in full and missing high
bits are explicitly false. This is an executable bit-list constructor, not
a finite source-tape loader. -/
namespace Shared.Beeping.NPcoNP.Source284BitWindowTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Codes.BitNumeralCompare (value)

/-- Produce precisely as many low-order bits as there are unary tokens. -/
def extract (p : List Bool × List Bool) : List Bool :=
  TM2ContextMapGeneric.contextMap TM2InputBitLookup.lookup
    (p.2,TM2UnaryRange.rangeFromTokens p.1)

theorem extract_isPolyTime : IsPolyTime extract := by
  let tokens : List Bool × List Bool → List Bool := fun p => p.1
  let bits : List Bool × List Bool → List Bool := fun p => p.2
  let indices : List Bool × List Bool → List Nat := fun p => TM2UnaryRange.rangeFromTokens (tokens p)
  have ht : IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hb : IsPolyTime bits := TM2GuardAllStep.second_isPolyTime
  have hi : IsPolyTime indices := TM2Compose.isPolyTime_comp tokens TM2UnaryRange.rangeFromTokens
    ht TM2UnaryRange.rangeFromTokens_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : List Bool × List Bool => (bits p,indices p))
    (TM2ContextMapGeneric.contextMap TM2InputBitLookup.lookup)
    (TM2GuardAllStep.pair_isPolyTime bits indices hb hi)
    (TM2ContextMapGeneric.contextMap_isPolyTime _ TM2InputBitLookup.lookup_isPolyTime)

theorem extract_length (tokens bits : List Bool) : (extract (tokens,bits)).length = tokens.length := by
  simp [extract,TM2ContextMapGeneric.contextMap,TM2UnaryRange.rangeFromTokens]

theorem extract_get (tokens bits : List Bool) (i : Nat) (hi : i < tokens.length) :
    (extract (tokens,bits))[i]'(by simpa [extract_length] using hi) = (bits[i]?).getD false := by
  simp [extract,TM2ContextMapGeneric.contextMap,TM2UnaryRange.rangeFromTokens,
    TM2InputBitLookup.lookup_correct]

/-- Raw lists may have redundant high zeroes; their numeric value nevertheless
has exactly the same bit at every index, including virtual false beyond the end. -/
theorem value_testBit (bits : List Bool) (i : Nat) :
    (value bits).testBit i = (bits[i]?).getD false := by
  induction bits generalizing i with
  | nil => simp [value]
  | cons b bs ih =>
    have hbit : value (b::bs) = Nat.bit b (value bs) := by
      cases b <;> simp [value,Nat.bit]
    cases i with
    | zero => simp [hbit]
    | succ i => simpa [hbit,Nat.testBit_bit_succ] using ih i

/-- The produced low bits denote exactly the binary residue modulo the
window; no assumption of a canonical input bit list is needed. -/
theorem extract_value (tokens bits : List Bool) :
    value (extract (tokens,bits)) = value bits % 2^tokens.length := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [value_testBit,Nat.testBit_mod_two_pow,value_testBit]
  by_cases hi : i < tokens.length
  · have hi' : i < (extract (tokens,bits)).length := by simpa [extract_length] using hi
    rw [List.getElem?_eq_getElem hi',Option.getD_some,extract_get tokens bits i hi]
    simp [hi]
  · have hnone : (extract (tokens,bits))[i]? = none :=
      List.getElem?_eq_none (by simpa [extract_length] using Nat.le_of_not_gt hi)
    simp [hi,hnone]

/-- Pointwise equality with the independently defined canonical numeric
window, including its virtual-zero padding. -/
theorem extract_eq_window (tokens bits : List Bool) :
    extract (tokens,bits) = Source284CanonicalPairWindow.window tokens.length (value bits) := by
  apply Source284CanonicalPairWindow.same_length_value_injective
  · simp [extract_length,Source284CanonicalPairWindow.window_length]
  · rw [extract_value,Source284CanonicalPairWindow.window_value]

namespace Fixtures
example : extract ([],[true,true]) = [] := by decide +kernel
example : extract ([true,true,true,true],[true,false]) = [true,false,false,false] := by decide +kernel
example : extract ([true,true],[true,false,true]) = [true,false] := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284BitWindowTM2
