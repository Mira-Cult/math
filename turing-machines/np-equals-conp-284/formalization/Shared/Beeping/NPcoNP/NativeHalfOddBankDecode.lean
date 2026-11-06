import Shared.Beeping.NPcoNP.NativeHalfOddBank
import Shared.Beeping.NPcoNP.Bootstrap284BankDecode

/-! Decode the physical bank left by the odd residual path using the shared
unary decoder. This is a mathematical tape observation, not a runtime oracle. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddBankDecode

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.NativeHalfOddBank
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- After the prepared odd path returns to state 1, decoding the physical
bank recovers the original suffix followed by exactly `(m+1)/2` zeros; the
two following bits are the additional reserve `10`. -/
theorem prepared_odd_to1_decodes (base : Int → Bool) (b z : Int) (m : Nat)
    (xs : List Nat) (hodd : m%2=1) (hz : ∀ p ≤ z, base p=false) :
    ∃ (n₁ n₂ : Nat) (head gap : Int) (finalTape : Int → Bool),
      0<n₁ ∧ 0<n₂ ∧ b≤gap ∧
      let values := xs ++ List.replicate ((m+1)/2) 0
      let word := encode values
      decode (xs.length+(m+1)/2) (readCells finalTape (gap+2) word.length) = some (values,[]) ∧
      finalTape (gap+2+(word.length : Int))=true ∧
      finalTape (gap+3+(word.length : Int))=false ∧
      silentSegment machine (cfg 30 b (prepared base b m xs))
        (cfg 1 (head-(n₂ : Int)) finalTape) (n₁+n₂) := by
  obtain ⟨n₁,n₂,head,gap,outBase,t,hn₁,hn₂,hgap,_,_,_,_,_,hbits,hreserve0,hreserve1,hseg⟩ :=
    prepared_odd_to1_bank base b z m xs hodd hz
  let values := xs ++ List.replicate ((m+1)/2) 0
  let word := encode values
  have hh : Holds t (gap+2) word := by
    apply holds_of_get
    intro i hi
    have ht := hbits i hi
    change t (gap+2+(i : Int))=bitAt word i at ht
    simpa only [bitAt,List.getElem?_eq_getElem hi,Option.getD_some] using ht
  have hr := read_of_holds t (gap+2) word hh
  have hd : decode (xs.length+(m+1)/2) word=some (values,[]) := by
    have h := decode_encode values []
    simpa only [List.append_nil,values,List.length_append,List.length_replicate] using h
  refine ⟨n₁,n₂,head,gap,t,hn₁,hn₂,hgap,?_,hreserve0,hreserve1,hseg⟩
  rw [hr]
  exact hd

end Shared.Beeping.NPcoNP.NativeHalfOddBankDecode

#print axioms Shared.Beeping.NPcoNP.NativeHalfOddBankDecode.prepared_odd_to1_decodes
