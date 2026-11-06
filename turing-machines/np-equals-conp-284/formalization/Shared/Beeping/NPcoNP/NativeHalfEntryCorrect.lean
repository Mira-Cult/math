import Shared.Beeping.NPcoNP.NativeHalfEntryZero

/-! Unified zero and nonzero native-HALF entry contract for the literal
284-state table. The selected-entry layout is explicit; a compiler proof
must still show that graph operands reach it and interpret the return path. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEntryCorrect

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.NativeHalfEntryZero
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The selected block begins at `b-1` and has value `value`. The suffix
and final reserve are paid tape content, not implicit machine input. -/
def selectedTape (base : Int → Bool) (b : Int) (value : Nat) (xs : List Nat) : Int → Bool :=
  match value with
  | 0 => after base b (encode xs)
  | m+1 => entryTape base b m xs

theorem selectedTape_layout (base : Int → Bool) (b : Int) (value : Nat)
    (xs : List Nat) (hb : base (b-1)=true) :
    Holds (selectedTape base b value xs) (b-1)
      (block value ++ encode xs ++ [true,false,false]) := by
  cases value with
  | zero => exact zero_entry_layout base b xs hb
  | succ m => exact entry_layout base b m xs hb

/-- For every selected natural value, the literal table completes a positive
finite silent segment to state 1. It leaves the selected quotient, preserves
all supplied suffix values, appends `(value+1)/2` zero blocks, and keeps the
separate final `10` reserve. The output head and duration are existential. -/
theorem selected_entry_quotient_and_bank (base : Int → Bool) (b z : Int)
    (value : Nat) (xs : List Nat) (hb : base (b-1)=true)
    (hz : ∀ p≤z, base p=false) :
    ∃ (steps : Nat) (head gap : Int) (finalTape : Int → Bool), 0<steps ∧
      Holds finalTape (b-1) (block (value/2)) ∧
      let values := xs ++ List.replicate ((value+1)/2) 0
      let word := encode values
      decode (xs.length+((value+1)/2)) (readCells finalTape (gap+2) word.length)=some (values,[]) ∧
      finalTape (gap+2+(word.length : Int))=true ∧
      finalTape (gap+3+(word.length : Int))=false ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value xs))
        (cfg 1 head finalTape) steps := by
  cases value with
  | zero =>
    obtain ⟨n₁,n₂,head,t,hn₁,hn₂,hquot,hdec,hr0,hr1,hseg⟩ :=
      entry_zero_quotient_and_bank base b z xs hb hz
    refine ⟨2+n₁+n₂,head,b-1,t,by omega,?_,?_,?_,?_,?_⟩
    · exact hquot
    · have he : b-1+2=b+1 := by omega
      simpa only [show (0+1)/2=0 by decide,List.replicate_zero,List.append_nil,Nat.add_zero,he] using hdec
    · have he : b-1+2=b+1 := by omega
      simpa only [show (0+1)/2=0 by decide,List.replicate_zero,List.append_nil,he] using hr0
    · have he : b-1+3=b+2 := by omega
      simpa only [show (0+1)/2=0 by decide,List.replicate_zero,List.append_nil,he] using hr1
    · exact hseg
  | succ m =>
    obtain ⟨n,head,gap,t,hn,hquot,hdec,hr0,hr1,hseg⟩ :=
      entry_nonzero_quotient_and_bank base b z m xs hb hz
    have hc : (Nat.succ m+1)/2=m/2+1 := by omega
    refine ⟨n,head,gap,t,hn,?_,?_,?_,?_,?_⟩
    · simpa [Nat.succ_eq_add_one] using hquot
    · simpa only [hc] using hdec
    · simpa only [hc] using hr0
    · simpa only [hc] using hr1
    · exact hseg

end Shared.Beeping.NPcoNP.NativeHalfEntryCorrect

#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryCorrect.selectedTape_layout
#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryCorrect.selected_entry_quotient_and_bank
