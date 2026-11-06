import Shared.Beeping.NPcoNP.NativeHalfEntryZeroBanks
import Shared.Beeping.NPcoNP.NativeHalfEntryCorrect

/-! A literal-table native HALF entry, including both encoded banks. This
local contract does not establish selector reachability or the return ABI. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEntryAllBanks

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfEntryCorrect
open Shared.Beeping.NPcoNP.NativeHalfEntryZeroBanks
open Shared.Beeping.NPcoNP.NativeHalfEntryEvenValue
open Shared.Beeping.NPcoNP.NativeHalfEntryOddValue
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- From the specified two-zero header and selected-entry tape, the literal
machine returns to state 1 after a positive finite silent segment, preserving
both supplied banks, the quotient and the separately represented final reserve.
The right bank gains exactly `(value+1)/2` zero blocks. -/
theorem selected_entry_preserves_banks (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right : List Nat) (hz : ∀ p≤z, back p=false) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    ∃ (steps : Nat) (head gap : Int) (finalTape : Int → Bool), 0<steps ∧
      (value%2=1 → head=ctrl-1) ∧
      (value%2=0 → head≤ctrl-2) ∧
      (value%2=0 → back (head+1)=false) ∧
      (value%2=0 → ∀ p, head+1<p → p<ctrl → back p=true) ∧
      (value%2=0 → ∀ p, head+2≤p → p<ctrl → finalTape p=false) ∧
      (value%2=1 → ∀ p<ctrl, finalTape p=back p) ∧
      (value%2=0 → ∀ p≤head+1, finalTape p=back p) ∧
      finalTape (head+1)=false ∧
      finalTape ctrl=false ∧ finalTape (ctrl+1)=false ∧
      gap=b+((value/2 : Nat) : Int)-1 ∧
      Holds finalTape (ctrl+2) (encode left) ∧
      Holds finalTape (b-1) (block (value/2)) ∧
      let values := right ++ List.replicate ((value+1)/2) 0
      let word := encode values
      Holds finalTape (gap+2) word ∧
      decode (right.length+((value+1)/2)) (readCells finalTape (gap+2) word.length)=some (values,[]) ∧
      finalTape (gap+2+(word.length : Int))=true ∧
      finalTape (gap+3+(word.length : Int))=false ∧
      (∀ p, gap+3+(word.length : Int)≤p → finalTape p=false) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 1 head finalTape) steps := by
  dsimp only
  cases value with
  | zero =>
    obtain ⟨n,head,t,hn,hhead,hstopBack,honesBack,hclear,hback,hstop,hctrl,hctrl1,hleft,hquot,hword,hdec,hr0,hr1,htail,hseg⟩ :=
      zero_value_entry_preserves_banks back ctrl z left right hz
    let b := ctrl+2+((leftSuffix left).length : Int)
    refine ⟨n,head,b-1,t,hn,by omega,fun _ => hhead,fun _ => hstopBack,fun _ => honesBack,fun _ => hclear,by omega,
      fun _ => hback,hstop,hctrl,hctrl1,
      by dsimp [b]; omega,hleft,hquot,?_,?_,?_,?_,?_,?_⟩
    · have he : b-1+2=b+1 := by omega
      simpa only [show (0+1)/2=0 by decide,List.replicate_zero,List.append_nil,he] using hword
    · have he : b-1+2=b+1 := by omega
      simpa only [show (0+1)/2=0 by decide,List.replicate_zero,List.append_nil,Nat.add_zero,he] using hdec
    · have he : b-1+2=b+1 := by omega
      simpa only [show (0+1)/2=0 by decide,List.replicate_zero,List.append_nil,he] using hr0
    · have he : b-1+3=b+2 := by omega
      simpa only [show (0+1)/2=0 by decide,List.replicate_zero,List.append_nil,he] using hr1
    · have he : b-1+3=b+2 := by omega
      simpa only [show (0+1)/2=0 by decide,List.replicate_zero,List.append_nil,he] using htail
    · exact hseg
  | succ m =>
    have hc : (Nat.succ m+1)/2=m/2+1 := by omega
    by_cases he : m%2=0
    · obtain ⟨n,head,gap,t,hn,hhead,hback,hctrl,hctrl1,hgap,hleft,hquot,hword,hdec,hr0,hr1,htail,hseg⟩ :=
        odd_value_entry_preserves_banks back ctrl z m left right he hz
      refine ⟨n,head,gap,t,hn,fun _ => hhead,by omega,by omega,by omega,by omega,fun _ => hback,
        by omega,by simpa [hhead] using hctrl,hctrl,hctrl1,
        ?_,hleft,?_,?_,?_,?_,?_,?_,?_⟩
      · simpa [Nat.succ_eq_add_one] using hgap
      · simpa [Nat.succ_eq_add_one] using hquot
      · simpa only [hc] using hword
      · simpa only [hc] using hdec
      · simpa only [hc] using hr0
      · simpa only [hc] using hr1
      · simpa only [hc] using htail
      · exact hseg
    · have ho : m%2=1 := by omega
      obtain ⟨n,head,gap,t,hn,hhead,hstopBack,honesBack,hclear,hback,hstop,hctrl,hctrl1,hgap,hleft,hquot,hword,hdec,hr0,hr1,htail,hseg⟩ :=
        even_value_entry_preserves_banks back ctrl z m left right ho hz
      refine ⟨n,head,gap,t,hn,by omega,fun _ => hhead,fun _ => hstopBack,fun _ => honesBack,fun _ => hclear,by omega,
        fun _ => hback,hstop,hctrl,hctrl1,
        ?_,hleft,?_,?_,?_,?_,?_,?_,?_⟩
      · simpa [Nat.succ_eq_add_one] using hgap
      · simpa [Nat.succ_eq_add_one] using hquot
      · simpa only [hc] using hword
      · simpa only [hc] using hdec
      · simpa only [hc] using hr0
      · simpa only [hc] using hr1
      · simpa only [hc] using htail
      · exact hseg


/-- The complete output bank is contiguous on the physical tape. -/
theorem selected_entry_packed_bank (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right : List Nat) (hz : ∀ p≤z, back p=false) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let values := left ++ [value/2] ++ right ++ List.replicate ((value+1)/2) 0
    ∃ (steps : Nat) (head : Int) (finalTape : Int → Bool), 0<steps ∧
      (value%2=1 → head=ctrl-1) ∧
      (value%2=0 → head≤ctrl-2) ∧
      (value%2=0 → back (head+1)=false) ∧
      (value%2=0 → ∀ p, head+1<p → p<ctrl → back p=true) ∧
      (value%2=0 → ∀ p, head+2≤p → p<ctrl → finalTape p=false) ∧
      (value%2=1 → ∀ p<ctrl, finalTape p=back p) ∧
      (value%2=0 → ∀ p≤head+1, finalTape p=back p) ∧
      finalTape (head+1)=false ∧
      finalTape ctrl=false ∧ finalTape (ctrl+1)=false ∧
      Holds finalTape (ctrl+2) (encode values) ∧
      finalTape (ctrl+2+((encode values).length : Int))=true ∧
      finalTape (ctrl+3+((encode values).length : Int))=false ∧
      (∀ p, ctrl+3+((encode values).length : Int)≤p → finalTape p=false) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 1 head finalTape) steps := by
  dsimp only
  obtain ⟨n,head,gap,t,hn,hhead,heven,hstopBack,honesBack,hclear,hoddback,hevenback,hstop,hctrl,hctrl1,hgap,hleft,hquot,hword,hdec,hr0,hr1,htail,hseg⟩ :=
    selected_entry_preserves_banks back ctrl z value left right hz
  let b := ctrl+2+((leftSuffix left).length : Int)
  let vs := right ++ List.replicate ((value+1)/2) 0
  let word := encode vs
  have hqpos : ctrl+2+((encode left).length : Int)=b-1 := by
    dsimp [b,leftSuffix]
    simp
    omega
  have hwpos : b-1+((block (value/2)).length : Int)=gap+2 := by
    rw [hgap]
    simp [block_length]
    omega
  have hjoined := holds_append t (ctrl+2) (encode left) (block (value/2)) hleft (by rw [hqpos]; exact hquot)
  have hword' : Holds t (ctrl+2+((encode left ++ block (value/2)).length : Int)) word := by
    have he : ctrl+2+((encode left ++ block (value/2)).length : Int)=gap+2 := by
      simp only [List.length_append,Nat.cast_add]
      rw [← Int.add_assoc,hqpos,hwpos]
    rw [he]
    exact hword
  have hall := holds_append t (ctrl+2) (encode left ++ block (value/2)) word hjoined hword'
  have hbits : Holds t (ctrl+2) (encode (left ++ [value/2] ++ vs)) := by
    simpa [encode_append,encode,List.append_assoc,word] using hall
  have hend : ctrl+2+((encode (left ++ [value/2] ++ vs)).length : Int)=gap+2+(word.length : Int) := by
    simp only [encode_append,encode_single,List.length_append,Nat.cast_add]
    rw [← Int.add_assoc,← Int.add_assoc,hqpos,hwpos]
  refine ⟨n,head,t,hn,hhead,heven,hstopBack,honesBack,hclear,hoddback,hevenback,hstop,hctrl,hctrl1,?_,?_,?_,?_,hseg⟩
  · simpa only [List.append_assoc,vs] using hbits
  · change t (gap+2+(word.length : Int))=true at hr0
    rw [← hend] at hr0
    simpa only [List.append_assoc,vs] using hr0
  · have hend' : ctrl+3+((encode (left ++ [value/2] ++ vs)).length : Int)=gap+3+(word.length : Int) := by omega
    change t (gap+3+(word.length : Int))=false at hr1
    rw [← hend'] at hr1
    simpa only [List.append_assoc,vs] using hr1
  · have hend' : ctrl+3+((encode (left ++ [value/2] ++ vs)).length : Int)=gap+3+(word.length : Int) := by omega
    intro p hp
    apply htail p
    have hp' : ctrl+3+((encode (left ++ [value/2] ++ vs)).length : Int)≤p := by
      simpa only [List.append_assoc,vs] using hp
    rwa [hend'] at hp'

end Shared.Beeping.NPcoNP.NativeHalfEntryAllBanks

#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryAllBanks.selected_entry_preserves_banks
#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryAllBanks.selected_entry_packed_bank
