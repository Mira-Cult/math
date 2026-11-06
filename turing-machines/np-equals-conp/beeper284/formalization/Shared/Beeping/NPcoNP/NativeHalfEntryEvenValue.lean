import Shared.Beeping.NPcoNP.NativeHalfReturnContext
import Shared.Beeping.NPcoNP.NativeHalfOddQuotient
import Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
import Shared.Beeping.NPcoNP.NativeHalfReturn23BankExact
import Shared.Beeping.NPcoNP.NativeHalfPrepared25Bank
import Shared.Beeping.NPcoNP.NativeHalfState95Stop

/-! Nonzero even selected values in a bank context: both the left and right
register banks are preserved through the literal native-HALF entry. The
graph selector and interpretation of the return-control path are separate. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEntryEvenValue

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfPrefixNo00
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfOddQuotient
open Shared.Beeping.NPcoNP.NativeHalfReturn23BankExact
open Shared.Beeping.NPcoNP.NativeHalfPrepared25Bank
open Shared.Beeping.NPcoNP.NativeHalfState95Stop
open Shared.Beeping.NPcoNP.NativeHalfOddBank
open Shared.Beeping.NPcoNP.NativeHalfOddFinish
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- With an explicit two-zero header and an encoded left bank, an odd
residual (equivalently a nonzero even selected value) returns silently with
the selected quotient and both supplied banks preserved. -/
theorem even_value_entry_preserves_banks (back : Int → Bool) (ctrl z : Int)
    (m : Nat) (left right : List Nat) (ho : m%2=1) (hz : ∀ p≤z, back p=false) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    ∃ (steps : Nat) (head gap : Int) (finalTape : Int → Bool), 0<steps ∧
      head≤ctrl-2 ∧
      back (head+1)=false ∧
      (∀ p, head+1<p → p<ctrl → back p=true) ∧
      (∀ p, head+2≤p → p<ctrl → finalTape p=false) ∧
      (∀ p≤head+1, finalTape p=back p) ∧
      finalTape (head+1)=false ∧
      finalTape ctrl=false ∧ finalTape (ctrl+1)=false ∧
      gap=b+(((m+1)/2 : Nat) : Int)-1 ∧
      Holds finalTape (ctrl+2) (encode left) ∧
      Holds finalTape (b-1) (block ((m+1)/2)) ∧
      let values := right ++ List.replicate (m/2+1) 0
      let word := encode values
      Holds finalTape (gap+2) word ∧
      decode (right.length+(m/2+1)) (readCells finalTape (gap+2) word.length)=some (values,[]) ∧
      finalTape (gap+2+(word.length : Int))=true ∧
      finalTape (gap+3+(word.length : Int))=false ∧
      (∀ p, gap+3+(word.length : Int)≤p → finalTape p=false) ∧
      silentSegment machine (cfg 29 (b-1) (entryTape base b m right))
        (cfg 1 head finalTape) steps := by
  dsimp only
  let base := before back ctrl (leftSuffix left)
  let b := ctrl+2+((leftSuffix left).length : Int)
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
  obtain ⟨n₁,gap,outBase,hn₁,hgap,hprefix,hfilled,hclean⟩ :=
    prepared_odd_to25_bank base b m right ho
  let values := right ++ List.replicate (m/2+1) 0
  let word := encode values
  have hcount : (m+1)/2=m/2+1 := by omega
  rw [hcount] at hclean
  let t := after outBase (gap+1) word
  let head := ctrl-1
  have hhead' : head<ctrl := by dsimp [head]; omega
  have hbg : b≤gap := by rw [hgap]; omega
  have hscanGap : gap=b+((m/2+1 : Nat) : Int)-1 := by
    have hnum : (m-1)/2+1=m/2+1 := by omega
    rw [hgap]
    omega
  let nscan := (leftSuffix left).length+(m/2+1)+2
  have hscan := return25_encoded_filled back outBase ctrl b gap left word (m/2+1)
    rfl hscanGap hprefix hfilled
  have hfirst := segAdd machine _ _ _ n₁ nscan hclean hscan
  let a := min z (ctrl-1)
  let k := (head-min a head).toNat
  have hk : head-(k : Int)≤a := by
    have hn : 0≤head-min a head := by omega
    have he : (k : Int)=head-min a head := Int.toNat_of_nonneg hn
    omega
  have ht : t (head-(k : Int))=false := by
    have hza : a≤z := min_le_left _ _
    have hca : a≤ctrl-1 := min_le_right _ _
    change after outBase (gap+1) word (head-(k : Int))=false
    rw [after_prefix _ _ _ _ (by omega),hprefix _ (by omega)]
    change before back ctrl (leftSuffix left) (head-(k : Int))=false
    rw [before_prefix _ _ _ _ (by omega)]
    exact hz _ (by omega)
  obtain ⟨n₂,hn₂,_,hstop,hones,hsecond⟩ := scan95_exact_with_stop k head t ht
  let finalTape := clearRange t (head-(n₂ : Int)+2) (head+1)
  have hsafe : head<b-(1 : Int) := by omega
  have hleft : ∀ p, b-(1 : Int)≤p → p<b → base p=true := by
    intro p hp hp'
    have he : p=b-1 := by omega
    rw [he]
    exact hb
  have hquot := quotient_block_of_safe_return base outBase b gap head 1 m n₂ word
    (by decide) ho hgap hleft hprefix hfilled hsafe
  have hvalue : sourceValue 1 m=m+1 := by simp [sourceValue]
  have hquot' : Holds finalTape (b-1) (block ((m+1)/2)) := by
    simpa only [hvalue,Nat.cast_one] using hquot
  have hout : ∀ p≥ctrl, finalTape p=t p := by
    intro p hp
    have hn : ¬ (head-(n₂ : Int)+2≤p ∧ p<head+1) := by omega
    change (if head-(n₂ : Int)+2≤p ∧ p<head+1 then false else t p)=t p
    rw [if_neg hn]
  have hleft : Holds finalTape (ctrl+2) (encode left) := by
    apply holds_of_get
    intro i hi
    have hp : ctrl+2+(i : Int)<b := by dsimp [b,leftSuffix]; simp; omega
    have hg : ctrl+2+(i : Int)<gap+1 := by omega
    rw [hout _ (by omega)]
    change after outBase (gap+1) word (ctrl+2+(i : Int)) = _
    rw [after_prefix _ _ _ _ hg,hprefix _ hp]
    change before back ctrl (leftSuffix left) (ctrl+2+(i : Int)) = _
    rw [before_suffix_bit]
    simp only [leftSuffix,bitAt,List.getElem?_append_left hi,List.getElem?_eq_getElem hi,Option.getD_some]
  have hbits : ∀ i : Nat, i<word.length → finalTape (gap+2+(i : Int))=bitAt word i := by
    intro i hi
    rw [hout _ (by omega)]
    have h := after_suffix_bit outBase (gap+1) word i hi
    simpa only [Int.add_assoc,show (1 : Int)+1=2 by decide] using h
  have hr0 : finalTape (gap+2+(word.length : Int))=true := by
    rw [hout _ (by omega)]
    have h := (appended_zero_block outBase (gap+1) word).1
    simpa only [Int.add_assoc,show (1 : Int)+1=2 by decide] using h
  have hr1 : finalTape (gap+3+(word.length : Int))=false := by
    rw [hout _ (by omega)]
    have h := (appended_zero_block outBase (gap+1) word).2
    simpa only [Int.add_assoc,show (1 : Int)+2=3 by decide] using h
  have hrightTail : ∀ p, gap+3+(word.length : Int)≤p → finalTape p=false := by
    intro p hp
    rw [hout _ (by omega)]
    change after outBase (gap+1) word p=false
    apply after_tail_zero
    omega
  have hh : Holds finalTape (gap+2) word := by
    apply holds_of_get
    intro i hi
    have h := hbits i hi
    simpa only [bitAt,List.getElem?_eq_getElem hi,Option.getD_some] using h
  have hr := read_of_holds finalTape (gap+2) word hh
  have hd : decode (right.length+(m/2+1)) word=some (values,[]) := by
    have h := decode_encode values []
    simpa only [List.append_nil,values,List.length_append,List.length_replicate] using h
  have hprepared := segAdd machine _ _ _ (n₁+nscan) n₂ hfirst hsecond
  obtain ⟨hentry,hprep⟩ := entry_to_prepared_successor base b m right hb
  let rest := n₁+nscan+n₂-1
  have hlen : 1+rest=n₁+nscan+n₂ := by dsimp [rest]; omega
  rw [← hlen] at hprepared
  have hcont := silent_tail_one _ _ _ rest hprep hprepared
  have hgap' : gap=b+(((m+1)/2 : Nat) : Int)-1 := by
    have hn : (m-1)/2+1=(m+1)/2 := by omega
    rw [hgap]
    omega
  have hcleared : ∀ p, head-(n₂ : Int)+2≤p → p<ctrl → finalTape p=false := by
    intro p hp hp'
    change (if head-(n₂ : Int)+2≤p ∧ p<head+1 then false else t p)=false
    rw [if_pos (by dsimp [head]; omega)]
  have hback : ∀ p≤head-(n₂ : Int)+1, finalTape p=back p := by
    intro p hp
    have hn : ¬ (head-(n₂ : Int)+2≤p ∧ p<head+1) := by omega
    change (if head-(n₂ : Int)+2≤p ∧ p<head+1 then false else t p)=back p
    rw [if_neg hn]
    change after outBase (gap+1) word p=back p
    rw [after_prefix _ _ _ _ (by omega),hprefix _ (by omega)]
    exact before_prefix back ctrl p (leftSuffix left) (by omega)
  have hheader : finalTape ctrl=false ∧ finalTape (ctrl+1)=false := by
    have hbase := gap_cells back ctrl (leftSuffix left)
    constructor
    · rw [hout _ (by omega)]
      change after outBase (gap+1) word ctrl=false
      rw [after_prefix _ _ _ _ (by omega),hprefix _ (by omega)]
      exact hbase.1
    · rw [hout _ (by omega)]
      change after outBase (gap+1) word (ctrl+1)=false
      rw [after_prefix _ _ _ _ (by omega),hprefix _ (by omega)]
      exact hbase.2.1
  have hstop' : finalTape (head-(n₂ : Int)+1)=false := by
    change (if head-(n₂ : Int)+2≤head-(n₂ : Int)+1 ∧
      head-(n₂ : Int)+1<head+1 then false else t (head-(n₂ : Int)+1))=false
    rw [if_neg (by omega)]
    exact hstop
  have hstopBack : back (head-(n₂ : Int)+1)=false := by
    rw [← hback _ (by omega)]
    exact hstop'
  have honesBack : ∀ p, head-(n₂ : Int)+1<p → p<ctrl → back p=true := by
    intro p hp hp'
    have ht : t p=true := hones p hp (by dsimp [head]; omega)
    change after outBase (gap+1) word p=true at ht
    rw [after_prefix _ _ _ _ (by omega),hprefix _ (by omega)] at ht
    change before back ctrl (leftSuffix left) p=true at ht
    rw [before_prefix _ _ _ _ hp'] at ht
    exact ht
  refine ⟨2+rest,head-(n₂ : Int),gap,finalTape,by omega,by dsimp [head]; omega,
    hstopBack,honesBack,hcleared,hback,hstop',hheader.1,hheader.2,hgap',hleft,hquot',hh,?_,hr0,hr1,hrightTail,?_⟩
  · rw [hr]
    exact hd
  · exact segAdd machine _ _ _ 2 rest hentry hcont

end Shared.Beeping.NPcoNP.NativeHalfEntryEvenValue

#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryEvenValue.even_value_entry_preserves_banks
