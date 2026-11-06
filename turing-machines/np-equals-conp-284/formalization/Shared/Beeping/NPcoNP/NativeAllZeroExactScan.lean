import Shared.Beeping.NPcoNP.NativeAllZeroActualDelimiter
import Shared.Beeping.NPcoNP.NativeAllZeroNextUnit
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14

/-! Exact state-12 scan conditional on the tracked cycle delimiter.
No blank-start or graph-refinement claim is made here. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroExactScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentDispatch
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentTo261
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentExact
open Shared.Beeping.NPcoNP.NativeAllZeroReturnWindow
open Shared.Beeping.NPcoNP.NativeAllZeroActualDelimiter
open Shared.Beeping.NPcoNP.NativeAllZeroNextUnit
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentReturn
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

/-- The returned tape contains the exact run of ones and its delimiter
scanned by state 12. -/
theorem selected_scan_word (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool)
    (delimiter : outTape (a+30) (r+3) (selectorOutput a r v rest t) (a+35+(r : Int))=false) :
    let final := outTape (a+30) (r+3) (selectorOutput a r v rest t)
    let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
    let selected := clearAt (a+28) output
    Holds selected (a+30) (List.replicate (r+5) true ++ [false]) := by
  dsimp only
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t)
  let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
  let selected := clearAt (a+28) output
  have hprefix : Holds selected (a+30) (List.replicate (r+4) true) := by
    apply holds_of_get
    intro i hi
    have hbound : i<r+4 := by simpa using hi
    have hp : a+30≤a+30+(i : Int) ∧ a+30+(i : Int)<a+34+(r : Int) := by omega
    have hne : a+30+(i : Int)≠a+28 := by omega
    simp [selected,clearAt,hne,output,fillRange,hp]
  have hmarker : selected (a+34+(r : Int))=true := by
    have hm : final (a+34+(r : Int))=true := by
      have hp : a+30+1+((r+3 : Nat):Int)=a+34+(r : Int) := by push_cast; omega
      simpa only [final,hp] using return_marker (a+30) (r+3) (selectorOutput a r v rest t)
    have hne : a+34+(r : Int)≠a+28 := by omega
    simp [selected,clearAt,hne,output,fillRange,setAt,hm]
  have hzero : selected (a+35+(r : Int))=false := by
    have hne : a+35+(r : Int)≠a+28 := by omega
    simp [selected,clearAt,hne,output,fillRange,setAt,final,delimiter]
  have hpair : Holds selected (a+34+(r : Int)) [true,false] := by
    simp only [Holds]
    exact ⟨hmarker,by simpa only [show a+34+(r : Int)+1=a+35+(r : Int) by omega] using hzero,trivial⟩
  have hfull := holds_append_intro selected (a+30) (List.replicate (r+4) true) [true,false] hprefix (by
    have hp : a+30+((List.replicate (r+4) true).length : Int)=a+34+(r : Int) := by simp; omega
    rw [hp]
    exact hpair)
  have hword : List.replicate (r+4) true ++ [true,false] = List.replicate (r+5) true ++ [false] := by
    have hrep : List.replicate (r+5) true = List.replicate (r+4) true ++ [true] := by
      conv_lhs => rw [show r+5=(r+4)+1 by omega, List.replicate_succ']
    rw [hrep]
    simp [List.append_assoc]
  rw [hword] at hfull
  exact hfull

/-- State 12 reaches state 14 at the first bank cell after exactly `r+6`
silent, tape-preserving transitions. -/
theorem selected_scan_to_bank (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool)
    (delimiter : outTape (a+30) (r+3) (selectorOutput a r v rest t) (a+35+(r : Int))=false) :
    let final := outTape (a+30) (r+3) (selectorOutput a r v rest t)
    let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
    let selected := clearAt (a+28) output
    silentSegment machine (cfg 12 (a+30) selected) (cfg 14 (a+36+(r : Int)) selected) (r+6) := by
  dsimp only
  have hw := selected_scan_word a r v rest t delimiter
  have h := scan12 (r+5) (a+30) _ hw
  have hp : a+30+((r+5 : Nat):Int)+1=a+36+(r : Int) := by push_cast; omega
  have hc : r+5+1=r+6 := by omega
  simpa only [hp,hc] using h

/-- The supplied padded absent-marker cycle reaches state 14 exactly at
the first bank cell, with the bank and protected left tape intact. -/
theorem padded_absent_exact_next14_with_delimiter (a : Int) (r v : Nat) (rest : List Nat)
    (suffix : List Bool) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (absent : t (a-3)=false)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int))
      ((encode (v::rest) ++ [false,false,false]) ++ ([false,false] ++ suffix))) :
    ∃ mid : Config 284, mid.state=23 ∧
      let t1 := setAt (a+29) (setAt (a+30) mid.tape)
      let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
      let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
      let selected := clearAt (a+28) output
      silentSegment machine (cfg 93 a t) (cfg 14 (a+36+(r : Int)) selected)
        ((((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32))+28)+(r+6)) ∧
      Holds selected (a+36+(r : Int))
        ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) ∧
      selected (a-3)=false ∧ (∀ q, q<a+26 → selected q=t q) ∧
      final (a+35+(r : Int))=false := by
  obtain ⟨mid,hs,hseg,hwindow,hbefore,hmarker,hbit,hdelim,hbank,hleft⟩ :=
    padded_cycle_with_actual_delimiter a r v rest suffix t window left0 earlier marker nextZero h0 h1 hz hm delimiter bank
  let t1 := setAt (a+29) (setAt (a+30) mid.tape)
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
  have habsent : final (a-3)=false := hbefore.trans absent
  have hdispatch := marker_absent_dispatch a final hwindow habsent
  let word := markerWindow (List.replicate 13 0 ++ [0])
  have hsplit : word=[false,true] ++ word.drop 2 := by decide
  have hdrop : Holds final a (word.drop 2) := by
    have hw : Holds final (a-2) word := hwindow
    rw [hsplit] at hw
    have h := holds_append_tail final (a-2) [false,true] (word.drop 2) hw
    simpa using h
  have hlen : (word.drop 2).length=26 := by decide
  have h27 : final (a+27)=false := by
    have he : a+30-3=a+27 := by omega
    simpa only [final,he] using return_clears_after_marker (a+30) (r+3) (selectorOutput a r v rest t1)
  have hend : Holds final (a+26) [true,false] := by
    simp only [Holds]
    exact ⟨hmarker, by simpa only [show a+26+1=a+27 by omega] using h27, trivial⟩
  have hchanged := holds_append_intro final a (word.drop 2) [true,false] hdrop (by simpa [hlen] using hend)
  have h261 := absent_window_to261 final a hchanged
  have hreturn := (absent_return_exact a r v rest t1).2 hbit
  have hall := segAdd machine _ _ _
    (((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
      ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
      ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18))) 31 hseg hdispatch
  have hall' := segAdd machine _ _ _ _ 28 hall h261
  have hall'' := segAdd machine _ _ _ _ (r+8) hall' hreturn
  have hbankout : Holds output (a+36+(r : Int))
      ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) := by
    apply holds_transport final output _ _ hbank
    intro q hq _
    symm
    exact (absent_return_frames a r v rest t1 q (Or.inr (by omega))).2
  have hleftout : ∀ q, q<a+26 → output q=t q := by
    intro q hq
    calc
      output q = final q := (absent_return_frames a r v rest t1 q (Or.inl (by omega))).2
      _ = t q := hleft q hq
  let selected := clearAt (a+28) output
  obtain ⟨hnextWindow,hnextMarker⟩ := long_return_window a r v rest t t1 window hleftout
  have h93 := long_return_window_to93 a r output hnextWindow hnextMarker
  have h12 := next_window_to12 a r output hnextWindow
  have h14 := selected_scan_to_bank a r v rest t1 hdelim
  have hall93 := segAdd machine _ _ _ _ (r+32) hall'' h93
  have hall12 := segAdd machine _ _ _ _ 28 hall93 h12
  have hall14 := segAdd machine _ _ _ _ (r+6) hall12 h14
  have hbankselected : Holds selected (a+36+(r : Int))
      ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) := by
    apply holds_transport output selected _ _ hbankout
    intro q hq _
    symm
    change (if q=a+28 then false else output q)=output q
    rw [if_neg (by omega)]
  have hleftselected : ∀ q, q<a+26 → selected q=t q := by
    intro q hq
    calc
      selected q = output q := by
        change (if q=a+28 then false else output q)=output q
        rw [if_neg (by omega)]
      _ = t q := hleftout q hq
  have hmissing : selected (a-3)=false := (hleftselected _ (by omega)).trans absent
  exact ⟨mid,hs,hall14,hbankselected,hmissing,hleftselected,hdelim⟩

/-- Retain the earlier exact state-14 interface. -/
theorem padded_absent_exact_next14 (a : Int) (r v : Nat) (rest : List Nat)
    (suffix : List Bool) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (absent : t (a-3)=false)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int))
      ((encode (v::rest) ++ [false,false,false]) ++ ([false,false] ++ suffix))) :
    ∃ mid : Config 284, mid.state=23 ∧
      let t1 := setAt (a+29) (setAt (a+30) mid.tape)
      let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
      let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
      let selected := clearAt (a+28) output
      silentSegment machine (cfg 93 a t) (cfg 14 (a+36+(r : Int)) selected)
        ((((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32))+28)+(r+6)) ∧
      Holds selected (a+36+(r : Int))
        ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) ∧
      selected (a-3)=false ∧ (∀ q, q<a+26 → selected q=t q) := by
  obtain ⟨mid,hs,hseg,hbank,hmissing,hleft,_hdelim⟩ :=
    padded_absent_exact_next14_with_delimiter a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  exact ⟨mid,hs,hseg,hbank,hmissing,hleft⟩

/-- At the bank-aligned state-14 boundary, increment the first value while
preserving the two remaining zeros and arbitrary suffix. -/
theorem exact_increment_with_suffix (v : Nat) (rest : List Nat) (h : Int)
    (suffix : List Bool) (t : Int → Bool)
    (bank : Holds t h ((encode (v::rest) ++ [false,false,false]) ++ suffix)) :
    ∃ e : Config 284, e.state=23 ∧
      e.head=h+(((v+1)+(encode rest).length : Nat):Int) ∧
      Holds e.tape h ((encode ((v+1)::rest) ++ [false,false]) ++ suffix) ∧
      (∀ q, q<h → e.tape q=t q) ∧
      silentSegment machine (cfg 14 h t) e (v+3+(encode rest).length) := by
  let oldPrefix := encode (v::rest) ++ [false]
  let newPrefix := encode ((v+1)::rest)
  have hbank : Holds t h oldPrefix := by
    apply holds_prefix_word t h oldPrefix ([false,false] ++ suffix)
    simpa [oldPrefix,List.append_assoc] using bank
  obtain ⟨e,hs,hh,hout,hframe,hseg⟩ := encoded_increment v rest h t hbank
  have htail : Holds t (h+(oldPrefix.length : Int)) ([false,false] ++ suffix) := by
    have hw : Holds t h (oldPrefix ++ ([false,false] ++ suffix)) := by
      simpa [oldPrefix,List.append_assoc] using bank
    exact holds_append_tail t h oldPrefix ([false,false] ++ suffix) hw
  have heqlen : oldPrefix.length=newPrefix.length := by
    simp [oldPrefix,newPrefix,encode,block_length]
    omega
  have htail' : Holds e.tape (h+(newPrefix.length : Int)) ([false,false] ++ suffix) := by
    rw [← heqlen]
    apply holds_transport t e.tape _ _ htail
    intro q hq _
    symm
    apply hframe q
    right
    have hlen : oldPrefix.length=(v+3)+(encode rest).length := by
      simp [oldPrefix,encode,block_length]
      omega
    rw [hlen] at hq
    push_cast at *
    omega
  have hfull := holds_append_intro e.tape h newPrefix ([false,false] ++ suffix) hout htail'
  have hrewrite : newPrefix ++ ([false,false] ++ suffix) =
      (encode ((v+1)::rest) ++ [false,false]) ++ suffix := by
    simp [newPrefix,List.append_assoc]
  rw [hrewrite] at hfull
  exact ⟨e,hs,hh,hfull,fun q hq => hframe q (Or.inl hq),hseg⟩

/-- The prepared marker-absent cycle reaches the aligned bank increment,
which increases its first value and retains the supplied suffix. -/
theorem padded_absent_exact_increment (a : Int) (r v : Nat) (rest : List Nat)
    (suffix : List Bool) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (absent : t (a-3)=false)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int))
      ((encode (v::rest) ++ [false,false,false]) ++ ([false,false] ++ suffix))) :
    ∃ (mid e : Config 284), mid.state=23 ∧ e.state=23 ∧
      e.head=a+36+(r : Int)+(((v+1)+(encode (rest ++ [0])).length : Nat):Int) ∧
      silentSegment machine (cfg 93 a t) e
        (((((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32))+28)+(r+6))+
          (v+3+(encode (rest ++ [0])).length)) ∧
      Holds e.tape (a+36+(r : Int))
        ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) ∧
      e.tape (a-3)=false ∧ (∀ q, q<a+26 → e.tape q=t q) := by
  obtain ⟨mid,hs,hseg,hbank,hmissing,hleft⟩ :=
    padded_absent_exact_next14 a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  let t1 := setAt (a+29) (setAt (a+30) mid.tape)
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
  let selected := clearAt (a+28) output
  have hbank' : Holds selected (a+36+(r : Int))
      ((encode (v::(rest ++ [0])) ++ [false,false,false]) ++ suffix) := by
    simpa using hbank
  obtain ⟨e,he,hehead,hebank,heleft,heinc⟩ :=
    exact_increment_with_suffix v (rest ++ [0]) (a+36+(r : Int)) suffix selected hbank'
  have hall := segAdd machine _ _ _ _ (v+3+(encode (rest ++ [0])).length) hseg heinc
  have hleft' : ∀ q, q<a+26 → e.tape q=t q := by
    intro q hq
    calc
      e.tape q = selected q := heleft q (by omega)
      _ = t q := hleft q hq
  have hmissing' : e.tape (a-3)=false := (hleft' _ (by omega)).trans absent
  exact ⟨mid,e,hs,he,hehead,hall,hebank,hmissing',hleft'⟩

#print axioms padded_absent_exact_increment
#print axioms exact_increment_with_suffix
#print axioms padded_absent_exact_next14_with_delimiter
#print axioms padded_absent_exact_next14
#print axioms selected_scan_word
#print axioms selected_scan_to_bank
end Shared.Beeping.NPcoNP.NativeAllZeroExactScan
