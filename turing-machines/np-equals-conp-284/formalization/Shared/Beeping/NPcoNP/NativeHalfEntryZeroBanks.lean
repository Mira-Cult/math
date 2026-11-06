import Shared.Beeping.NPcoNP.NativeHalfEntryOddValue
import Shared.Beeping.NPcoNP.NativeHalfEntryZero

/-! Zero selected value in a supplied two-zero-header and left-bank
context. The graph selector and return-control interpretation remain open. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEntryZeroBanks

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfPrefixNo00
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfOddReturnPair
open Shared.Beeping.NPcoNP.NativeHalfOddFinish
open Shared.Beeping.NPcoNP.NativeHalfReturn23BankExact
open Shared.Beeping.NPcoNP.NativeHalfState95Stop
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.NativeHalfEntryZero
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- A zero-valued selected entry returns silently while preserving its
zero block, both supplied banks and the existing final `10` reserve. -/
theorem zero_value_entry_preserves_banks (back : Int → Bool) (ctrl z : Int)
    (left right : List Nat) (hz : ∀ p≤z, back p=false) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    ∃ (steps : Nat) (head : Int) (finalTape : Int → Bool), 0<steps ∧
      head≤ctrl-2 ∧
      back (head+1)=false ∧
      (∀ p, head+1<p → p<ctrl → back p=true) ∧
      (∀ p, head+2≤p → p<ctrl → finalTape p=false) ∧
      (∀ p≤head+1, finalTape p=back p) ∧
      finalTape (head+1)=false ∧
      finalTape ctrl=false ∧ finalTape (ctrl+1)=false ∧
      Holds finalTape (ctrl+2) (encode left) ∧ Holds finalTape (b-1) (block 0) ∧
      Holds finalTape (b+1) (encode right) ∧
      decode right.length (readCells finalTape (b+1) (encode right).length)=some (right,[]) ∧
      finalTape (b+1+((encode right).length : Int))=true ∧
      finalTape (b+2+((encode right).length : Int))=false ∧
      (∀ p, b+2+((encode right).length : Int)≤p → finalTape p=false) ∧
      silentSegment machine (cfg 29 (b-1) (after base b (encode right)))
        (cfg 1 head finalTape) steps := by
  dsimp only
  let base := before back ctrl (leftSuffix left)
  let b := ctrl+2+((leftSuffix left).length : Int)
  let t := after base b (encode right)
  have hb : base (b-1)=true := by
    have h := before_selected_one back ctrl left
    have he : b-1=ctrl+1+((leftSuffix left).length : Int) := by dsimp [b]; omega
    change before back ctrl (leftSuffix left) (b-1)=true
    rw [he]
    exact h
  have hbctrl : ctrl+2≤b-1 := by
    have hn : 0<((leftSuffix left).length : Int) := by exact_mod_cast suffix_length_pos left
    dsimp [b]
    omega
  have hleft : t (b-1)=true := by
    change after base b (encode right) (b-1)=true
    rw [after_prefix _ _ _ _ (by omega)]
    exact hb
  have hzero : t b=false := (gap_cells base b (encode right)).2.2
  have ha := oneSeg machine _ _ (step29_one (b-1) t hleft)
  have ha' : silentSegment machine (cfg 29 (b-1) t) (cfg 41 b t) 1 := by
    simpa only [Int.sub_add_cancel] using ha
  have hb' := oneSeg machine _ _ (step41_zero b t hzero)
  have hentry := segAdd machine _ _ _ 1 1 ha' hb'
  let a := min z (ctrl-1)
  let n₁ := (leftSuffix left).length+0+2
  let pos := ctrl-1
  have hposctrl : pos<ctrl := by dsimp [pos]; omega
  have hpref : ∀ p<b, base p=before back ctrl (leftSuffix left) p := by intro p hp; rfl
  have hfilled : ∀ p, b≤p → p≤b-1 → base p=true := by intro p hp hp'; omega
  have hreturn' := return25_encoded_filled back base ctrl b (b-1) left (encode right) 0
    rfl (by simp) hpref hfilled
  have hreturn : silentSegment machine (cfg 25 (b-1) t) (cfg 95 pos t) n₁ := by
    simpa only [Int.sub_add_cancel] using hreturn'
  let k' := (pos-min a pos).toNat
  have hk' : pos-(k' : Int)≤a := by
    have hn : 0≤pos-min a pos := by omega
    have he : (k' : Int)=pos-min a pos := Int.toNat_of_nonneg hn
    omega
  have ht' : t (pos-(k' : Int))=false := by
    have hza : a≤z := min_le_left _ _
    have hca : a≤ctrl-1 := min_le_right _ _
    change after base b (encode right) (pos-(k' : Int))=false
    rw [after_prefix _ _ _ _ (by omega)]
    change before back ctrl (leftSuffix left) (pos-(k' : Int))=false
    rw [before_prefix _ _ _ _ (by omega)]
    exact hz _ (by omega)
  obtain ⟨n₂,hn₂,_,hstop,hones,hfinish⟩ := scan95_exact_with_stop k' pos t ht'
  let finalTape := clearRange t (pos-(n₂ : Int)+2) (pos+1)
  have hout : ∀ p≥ctrl, finalTape p=t p := by
    intro p hp
    have hn : ¬ (pos-(n₂ : Int)+2≤p ∧ p<pos+1) := by omega
    change (if pos-(n₂ : Int)+2≤p ∧ p<pos+1 then false else t p)=t p
    rw [if_neg hn]
  have hleftBank : Holds finalTape (ctrl+2) (encode left) := by
    apply holds_of_get
    intro i hi
    have hp : ctrl+2+(i : Int)<b := by dsimp [b,leftSuffix]; simp; omega
    rw [hout _ (by omega)]
    change after base b (encode right) (ctrl+2+(i : Int)) = _
    rw [after_prefix _ _ _ _ hp]
    change before back ctrl (leftSuffix left) (ctrl+2+(i : Int)) = _
    rw [before_suffix_bit]
    simp only [leftSuffix,bitAt,List.getElem?_append_left hi,List.getElem?_eq_getElem hi,Option.getD_some]
  have hblock : Holds finalTape (b-1) (block 0) := by
    have h0 : finalTape (b-1)=true := by rw [hout _ (by omega)]; exact hleft
    have h1 : finalTape b=false := by rw [hout _ (by omega)]; exact hzero
    simpa only [block_zero,Holds,Int.sub_add_cancel] using And.intro h0 (And.intro h1 trivial)
  have hbits : ∀ i : Nat, i<(encode right).length →
      finalTape (b+1+(i : Int))=bitAt (encode right) i := by
    intro i hi
    rw [hout _ (by omega)]
    exact after_suffix_bit base b (encode right) i hi
  have hh : Holds finalTape (b+1) (encode right) := by
    apply holds_of_get
    intro i hi
    have hh := hbits i hi
    simpa only [bitAt,List.getElem?_eq_getElem hi,Option.getD_some] using hh
  have hr := read_of_holds finalTape (b+1) (encode right) hh
  have hd : decode right.length (encode right)=some (right,[]) := by
    have hh := decode_encode right []
    simpa only [List.append_nil] using hh
  have hr0 : finalTape (b+1+((encode right).length : Int))=true := by
    rw [hout _ (by omega)]
    exact (appended_zero_block base b (encode right)).1
  have hr1 : finalTape (b+2+((encode right).length : Int))=false := by
    rw [hout _ (by omega)]
    exact (appended_zero_block base b (encode right)).2
  have hrightTail : ∀ p, b+2+((encode right).length : Int)≤p → finalTape p=false := by
    intro p hp
    rw [hout _ (by omega)]
    change after base b (encode right) p=false
    apply after_tail_zero
    omega
  have hcleared : ∀ p, pos-(n₂ : Int)+2≤p → p<ctrl → finalTape p=false := by
    intro p hp hp'
    change (if pos-(n₂ : Int)+2≤p ∧ p<pos+1 then false else t p)=false
    rw [if_pos (by dsimp [pos]; omega)]
  have hback : ∀ p≤pos-(n₂ : Int)+1, finalTape p=back p := by
    intro p hp
    have hn : ¬ (pos-(n₂ : Int)+2≤p ∧ p<pos+1) := by omega
    change (if pos-(n₂ : Int)+2≤p ∧ p<pos+1 then false else t p)=back p
    rw [if_neg hn]
    change after base b (encode right) p=back p
    rw [after_prefix _ _ _ _ (by omega)]
    exact before_prefix back ctrl p (leftSuffix left) (by omega)
  have hheader : finalTape ctrl=false ∧ finalTape (ctrl+1)=false := by
    have hbase := gap_cells back ctrl (leftSuffix left)
    constructor
    · rw [hout _ (by omega)]
      change after base b (encode right) ctrl=false
      rw [after_prefix _ _ _ _ (by omega)]
      exact hbase.1
    · rw [hout _ (by omega)]
      change after base b (encode right) (ctrl+1)=false
      rw [after_prefix _ _ _ _ (by omega)]
      exact hbase.2.1
  have hstop' : finalTape (pos-(n₂ : Int)+1)=false := by
    change (if pos-(n₂ : Int)+2≤pos-(n₂ : Int)+1 ∧
      pos-(n₂ : Int)+1<pos+1 then false else t (pos-(n₂ : Int)+1))=false
    rw [if_neg (by omega)]
    exact hstop
  have hstopBack : back (pos-(n₂ : Int)+1)=false := by
    rw [← hback _ (by omega)]
    exact hstop'
  have honesBack : ∀ p, pos-(n₂ : Int)+1<p → p<ctrl → back p=true := by
    intro p hp hp'
    have ht : t p=true := hones p hp (by dsimp [pos]; omega)
    change after base b (encode right) p=true at ht
    rw [after_prefix _ _ _ _ (by omega)] at ht
    change before back ctrl (leftSuffix left) p=true at ht
    rw [before_prefix _ _ _ _ hp'] at ht
    exact ht
  refine ⟨2+n₁+n₂,pos-(n₂ : Int),finalTape,by omega,by dsimp [pos]; omega,
    hstopBack,honesBack,hcleared,hback,hstop',hheader.1,hheader.2,hleftBank,hblock,hh,?_,hr0,hr1,hrightTail,?_⟩
  · rw [hr]
    exact hd
  · exact segAdd machine _ _ _ (2+n₁) n₂ (segAdd machine _ _ _ 2 n₁ hentry hreturn) hfinish

end Shared.Beeping.NPcoNP.NativeHalfEntryZeroBanks

#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryZeroBanks.zero_value_entry_preserves_banks
