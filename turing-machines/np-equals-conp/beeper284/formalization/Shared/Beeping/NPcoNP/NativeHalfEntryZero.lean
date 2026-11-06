import Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
import Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress
import Shared.Beeping.NPcoNP.NativeHalfOddFinish

/-! The literal native-HALF zero-value entry. The prepared tape and finite
left tail are explicit; selector reachability and branch meaning are separate. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEntryZero

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress
open Shared.Beeping.NPcoNP.NativeHalfOddFinish
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem row41_zero : machine.table.row 41 false=⟨false,.left,25,false⟩ := by decide

theorem step41_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 41 h t)=(cfg 25 (h-1) t,false) := by
  have hw : (⟨41,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row41_zero,Move.apply,hw]

/-- A one followed by the gap zero is the selected zero-valued block. -/
theorem zero_entry_layout (base : Int → Bool) (b : Int) (xs : List Nat)
    (hb : base (b-1)=true) :
    Holds (after base b (encode xs)) (b-1) (block 0 ++ encode xs ++ [true,false,false]) := by
  let t := after base b (encode xs)
  have hleft : t (b-1)=true := by
    change after base b (encode xs) (b-1)=true
    rw [after_prefix _ _ _ _ (by omega)]
    exact hb
  have hzero : t b=false := (gap_cells base b (encode xs)).2.2
  have hh := NativeHalfCleanupScan.holds_after_suffix base b (encode xs)
  have hwords : Holds t (b-1) (true :: false :: (encode xs ++ [true,false,false])) := by
    change t (b-1)=true ∧ Holds t ((b-1)+1) (false :: (encode xs ++ [true,false,false]))
    refine ⟨hleft,?_⟩
    rw [show (b-1)+1=b by omega]
    exact ⟨hzero,hh⟩
  simpa [block,List.append_assoc] using hwords

/-- A prepared zero-valued entry takes a finite silent segment to state 1,
preserving the selected zero block, every suffix value and the existing `10`
reserve. Its return-control interpretation is not asserted here. -/
theorem entry_zero_quotient_and_bank (base : Int → Bool) (b z : Int) (xs : List Nat)
    (hb : base (b-1)=true) (hz : ∀ p≤z, base p=false) :
    ∃ (n₁ n₂ : Nat) (head : Int) (finalTape : Int → Bool), 0<n₁ ∧ 0<n₂ ∧
      Holds finalTape (b-1) (block 0) ∧
      decode xs.length (readCells finalTape (b+1) (encode xs).length)=some (xs,[]) ∧
      finalTape (b+1+((encode xs).length : Int))=true ∧
      finalTape (b+2+((encode xs).length : Int))=false ∧
      silentSegment machine (cfg 29 (b-1) (after base b (encode xs)))
        (cfg 1 head finalTape) (2+n₁+n₂) := by
  let t := after base b (encode xs)
  have hleft : t (b-1)=true := by
    change after base b (encode xs) (b-1)=true
    rw [after_prefix _ _ _ _ (by omega)]
    exact hb
  have hzero : t b=false := (gap_cells base b (encode xs)).2.2
  have ha := oneSeg machine _ _ (step29_one (b-1) t hleft)
  have ha' : silentSegment machine (cfg 29 (b-1) t) (cfg 41 b t) 1 := by
    simpa only [Int.sub_add_cancel] using ha
  have hb' := oneSeg machine _ _ (step41_zero b t hzero)
  have hentry := segAdd machine _ _ _ 1 1 ha' hb'
  let left := min z (b-1)
  let k := ((b-1)-min left (b-1)).toNat
  have hk : (b-1)-(k : Int)≤left := by
    have hn : 0≤(b-1)-min left (b-1) := by omega
    have he : (k : Int)=(b-1)-min left (b-1) := Int.toNat_of_nonneg hn
    omega
  have ht : ∀ p≤(b-1)-(k : Int), t p=false := by
    intro p hp
    have hza : left≤z := min_le_left _ _
    have hba : left≤b-1 := min_le_right _ _
    change after base b (encode xs) p=false
    rw [after_prefix _ _ _ _ (by omega)]
    exact hz p (by omega)
  obtain ⟨n₁,hn₁,_,hreturn⟩ := scan25_left_zero k (b-1) t ht false
  let pos := (b-1)-(n₁ : Int)
  have hpos : pos<b-1 := by dsimp [pos]; omega
  let k' := (pos-min left pos).toNat
  have hk' : pos-(k' : Int)≤left := by
    have hn : 0≤pos-min left pos := by omega
    have he : (k' : Int)=pos-min left pos := Int.toNat_of_nonneg hn
    omega
  have ht' : t (pos-(k' : Int))=false := ht _ (by dsimp [pos] at *; omega)
  obtain ⟨n₂,hn₂,_,hfinish⟩ := scan95_exact k' pos t ht'
  let finalTape := clearRange t (pos-(n₂ : Int)+2) (pos+1)
  have hout : ∀ p≥b-1, finalTape p=t p := by
    intro p hp
    have hn : ¬ (pos-(n₂ : Int)+2≤p ∧ p<pos+1) := by omega
    change (if pos-(n₂ : Int)+2≤p ∧ p<pos+1 then false else t p)=t p
    rw [if_neg hn]
  have hblock : Holds finalTape (b-1) (block 0) := by
    have hl : finalTape (b-1)=true := by rw [hout _ (by omega)]; exact hleft
    have hr : finalTape b=false := by rw [hout _ (by omega)]; exact hzero
    simpa only [block_zero,Holds,Int.sub_add_cancel] using And.intro hl (And.intro hr trivial)
  have hbits : ∀ i : Nat, i<(encode xs).length →
      finalTape (b+1+(i : Int))=bitAt (encode xs) i := by
    intro i hi
    rw [hout _ (by omega)]
    exact after_suffix_bit base b (encode xs) i hi
  have hh : Holds finalTape (b+1) (encode xs) := by
    apply holds_of_get
    intro i hi
    have he := hbits i hi
    simpa only [bitAt,List.getElem?_eq_getElem hi,Option.getD_some] using he
  have hr := read_of_holds finalTape (b+1) (encode xs) hh
  have hd : decode xs.length (encode xs)=some (xs,[]) := by
    have he := decode_encode xs []
    simpa only [List.append_nil] using he
  have hres0 : finalTape (b+1+((encode xs).length : Int))=true := by
    rw [hout _ (by omega)]
    exact (appended_zero_block base b (encode xs)).1
  have hres1 : finalTape (b+2+((encode xs).length : Int))=false := by
    rw [hout _ (by omega)]
    exact (appended_zero_block base b (encode xs)).2
  refine ⟨n₁,n₂,pos-(n₂ : Int),finalTape,hn₁,hn₂,hblock,?_,hres0,hres1,?_⟩
  · rw [hr]
    exact hd
  · exact segAdd machine _ _ _ (2+n₁) n₂ (segAdd machine _ _ _ 2 n₁ hentry hreturn) hfinish

end Shared.Beeping.NPcoNP.NativeHalfEntryZero

#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryZero.zero_entry_layout
#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryZero.entry_zero_quotient_and_bank
