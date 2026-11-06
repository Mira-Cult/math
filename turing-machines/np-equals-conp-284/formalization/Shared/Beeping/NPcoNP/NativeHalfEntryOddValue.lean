import Shared.Beeping.NPcoNP.NativeHalfEntryEvenValue
import Shared.Beeping.NPcoNP.NativeHalfEvenQuotient
import Shared.Beeping.NPcoNP.NativeHalfReturn23BankExact

/-! Nonzero odd selected values in an explicit left-bank context. The
selected-entry and return-control interpretations at graph level remain
separate from this local literal-table proof. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEntryOddValue

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfPrefixNo00
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfEvenBank
open Shared.Beeping.NPcoNP.NativeHalfEvenQuotient
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfReturn23BankExact
open Shared.Beeping.NPcoNP.NativeHalfEntryNonzero
open Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- An even residual (a nonzero odd selected value) returns silently with
the quotient and both supplied banks preserved. -/
theorem odd_value_entry_preserves_banks (back : Int → Bool) (ctrl z : Int)
    (m : Nat) (left right : List Nat) (he : m%2=0) (hz : ∀ p≤z, back p=false) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    ∃ (steps : Nat) (head gap : Int) (finalTape : Int → Bool), 0<steps ∧
      head=ctrl-1 ∧
      (∀ p<ctrl, finalTape p=back p) ∧
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
    have hp : b-1=ctrl+1+((leftSuffix left).length : Int) := by dsimp [b]; omega
    change before back ctrl (leftSuffix left) (b-1)=true
    rw [hp]
    exact h
  have hbctrl : ctrl+2≤b-1 := by
    have hn : 0<((leftSuffix left).length : Int) := by exact_mod_cast suffix_length_pos left
    dsimp [b]
    omega
  obtain ⟨n₁,gap,outBase,hn₁,hgap,hprefix,hfilled,hfirst⟩ :=
    prepared_even_to23_bank base b m right he
  let values := right ++ List.replicate (m/2+1) 0
  let word := encode values
  let t := after outBase (gap+1) word
  let n₂ := (leftSuffix left).length+m/2+2
  have hsecond := return23_encoded_filled back outBase ctrl b gap left word (m/2)
    rfl hgap hprefix hfilled
  have hleft : ∀ p, b-(1 : Int)≤p → p<b → base p=true := by
    intro p hp hp'
    have hp'' : p=b-1 := by omega
    rw [hp'']
    exact hb
  have hquot := quotient_block base outBase b gap 1 m word (by decide) he hgap hleft hprefix hfilled
  have hvalue : sourceValue 1 m=m+1 := by simp [sourceValue]
  have hquot' : Holds t (b-1) (block ((m+1)/2)) := by simpa only [hvalue,Nat.cast_one] using hquot
  have hleftBank : Holds t (ctrl+2) (encode left) := by
    apply holds_of_get
    intro i hi
    have hp : ctrl+2+(i : Int)<b := by dsimp [b,leftSuffix]; simp; omega
    have hg : ctrl+2+(i : Int)<gap+1 := by rw [hgap]; omega
    change after outBase (gap+1) word (ctrl+2+(i : Int)) = _
    rw [after_prefix _ _ _ _ hg,hprefix _ hp]
    change before back ctrl (leftSuffix left) (ctrl+2+(i : Int)) = _
    rw [before_suffix_bit]
    simp only [leftSuffix,bitAt,List.getElem?_append_left hi,List.getElem?_eq_getElem hi,Option.getD_some]
  have hbits : ∀ i : Nat, i<word.length → t (gap+2+(i : Int))=bitAt word i := by
    intro i hi
    have hh := after_suffix_bit outBase (gap+1) word i hi
    simpa only [Int.add_assoc,show (1 : Int)+1=2 by decide] using hh
  have hr0 : t (gap+2+(word.length : Int))=true := by
    have hh := (appended_zero_block outBase (gap+1) word).1
    simpa only [Int.add_assoc,show (1 : Int)+1=2 by decide] using hh
  have hr1 : t (gap+3+(word.length : Int))=false := by
    have hh := (appended_zero_block outBase (gap+1) word).2
    simpa only [Int.add_assoc,show (1 : Int)+2=3 by decide] using hh
  have hrightTail : ∀ p, gap+3+(word.length : Int)≤p → t p=false := by
    intro p hp
    change after outBase (gap+1) word p=false
    apply after_tail_zero
    omega
  have hh : Holds t (gap+2) word := by
    apply holds_of_get
    intro i hi
    have hh := hbits i hi
    simpa only [bitAt,List.getElem?_eq_getElem hi,Option.getD_some] using hh
  have hr := read_of_holds t (gap+2) word hh
  have hd : decode (right.length+(m/2+1)) word=some (values,[]) := by
    have hh := decode_encode values []
    simpa only [List.append_nil,values,List.length_append,List.length_replicate] using hh
  have hprepared := segAdd machine _ _ _ n₁ n₂ hfirst hsecond
  obtain ⟨hentry,hprep⟩ := entry_to_prepared_successor base b m right hb
  let rest := n₁+n₂-1
  have hlen : 1+rest=n₁+n₂ := by dsimp [rest]; omega
  rw [← hlen] at hprepared
  have hcont := silent_tail_one _ _ _ rest hprep hprepared
  have hgap' : gap=b+(((m+1)/2 : Nat) : Int)-1 := by
    have hn : (m+1)/2=m/2 := by omega
    rw [hn]
    exact hgap
  have hprefixBack : ∀ p<ctrl, t p=back p := by
    intro p hp
    change after outBase (gap+1) word p=back p
    rw [after_prefix _ _ _ _ (by omega),hprefix _ (by omega)]
    exact before_prefix back ctrl p (leftSuffix left) hp
  have hheader : t ctrl=false ∧ t (ctrl+1)=false := by
    have hbase := gap_cells back ctrl (leftSuffix left)
    constructor
    · change after outBase (gap+1) word ctrl=false
      rw [after_prefix _ _ _ _ (by omega),hprefix _ (by omega)]
      exact hbase.1
    · change after outBase (gap+1) word (ctrl+1)=false
      rw [after_prefix _ _ _ _ (by omega),hprefix _ (by omega)]
      exact hbase.2.1
  refine ⟨2+rest,ctrl-1,gap,t,by omega,rfl,hprefixBack,hheader.1,hheader.2,
    hgap',hleftBank,hquot',hh,?_,hr0,hr1,hrightTail,?_⟩
  · rw [hr]
    exact hd
  · exact segAdd machine _ _ _ 2 rest hentry hcont

end Shared.Beeping.NPcoNP.NativeHalfEntryOddValue

#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryOddValue.odd_value_entry_preserves_banks
