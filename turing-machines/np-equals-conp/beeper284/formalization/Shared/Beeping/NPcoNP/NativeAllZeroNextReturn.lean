import Shared.Beeping.NPcoNP.NativeAllZeroExactScan
import Shared.Beeping.NPcoNP.NativeUnit261Return1

/-! Exact return through the incremented bank to the nearer two-zero pair.
The supplied prepared layout is not a blank-start or graph invariant. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentReturn
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentDispatch
open Shared.Beeping.NPcoNP.NativeAllZeroExactScan
open Shared.Beeping.NPcoNP.NativeAllZeroReturnWindow
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfReturn23
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeIncReturn23
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000
attribute [local irreducible] machine

/-- A nonempty encoded bank and one-run return to the two supplied zeros.
The scan is exact, silent, and leaves the whole tape unchanged. -/
theorem bank_run_to1 (v : Nat) (rest : List Nat) (h : Int) (r : Nat) (t : Int → Bool)
    (hr : 0<r) (h0 : t h=false) (h1 : t (h+1)=false)
    (run : Holds t (h+2) (List.replicate r true ++ [false]))
    (bank : Holds t (h+2+(r : Int)+1) (encode (v::rest))) :
    let base := h+2+(r : Int)+1
    silentSegment machine (cfg 23 (base+((encode (v::rest)).length : Int)-2) t)
      (cfg 1 (h-1) t) ((encode (v::rest)).length+r+2) := by
  dsimp only
  let base := h+2+(r : Int)+1
  let values := v::rest
  obtain ⟨front,hfront⟩ := encode_ends_zero values (by simp [values])
  have hlen : (encode values).length=front.length+1 := by rw [hfront]; simp
  have hprefix : Prefix (false::front.reverse) := by
    have ht := prefix_reverse_bank values
    rw [hfront] at ht
    simpa using ht
  have hpfront : Prefix front.reverse := prefix_tail_after_zero _ hprefix
  have hptail : Prefix (false::List.replicate r true) := by
    cases r with
    | zero => omega
    | succ n =>
      simp only [List.replicate_succ]
      exact Prefix.zeroOne (prefix_ones n)
  obtain ⟨shape,hshape⟩ := shape_of_prefix
    (front.reverse ++ (false::List.replicate r true)) (prefix_append hpfront hptail)
  have hword : Holds t base front := by
    have hh : Holds t base (front++[false]) := by rw [←hfront]; exact bank
    exact holds_prefix t base front [false] hh
  have hreverse := holds_reverse t base front hword
  have hscanrev := holds_reverse t (h+2) (List.replicate r true ++ [false]) run
  have hstart : h+2+(((List.replicate r true ++ [false]).length : Nat):Int)-1=base-1 := by
    simp [base]
    omega
  rw [hstart] at hscanrev
  have hscanrev' : downHolds t (base-1) (false::List.replicate r true) := by
    simpa using hscanrev
  have hzeros : downHolds t (h+1) [false,false] := by
    change t (h+1)=false ∧ t (h+1-1)=false ∧ True
    have he : h+1-1=h := by omega
    exact ⟨h1,by rw [he]; exact h0,trivial⟩
  have htail : downHolds t (base-1) ((false::List.replicate r true)++[false,false]) := by
    apply down_append t _ (false::List.replicate r true) [false,false] hscanrev'
    have he : base-1-(((false::List.replicate r true).length : Nat):Int)=h+1 := by
      simp [base]
      omega
    rw [he]
    exact hzeros
  have hall : downHolds t (base+(front.length : Int)-1)
      ((front.reverse ++ (false::List.replicate r true)) ++ [false,false]) := by
    have he : base+(front.length : Int)-1-((front.reverse.length : Nat):Int)=base-1 := by simp; omega
    have ht := down_append t _ front.reverse
      ((false::List.replicate r true)++[false,false]) hreverse (by rw [he]; exact htail)
    simpa only [List.append_assoc] using ht
  rw [←hshape] at hall
  have hret := return_scan shape (base+(front.length : Int)-1) t hall
  have hshapeLen : (bits shape).length=front.length+1+r := by
    rw [hshape]
    simp only [List.length_append,List.length_reverse,List.length_cons,List.length_replicate]
    omega
  have hstartBank : base+(front.length : Int)-1=base+((encode values).length : Int)-2 := by
    rw [hlen]
    omega
  have hend : base+(front.length : Int)-1-((bits shape).length : Int)-2=h-1 := by
    rw [hshapeLen]
    dsimp [base]
    omega
  have hcost : (bits shape).length+2=(encode values).length+r+2 := by omega
  rw [hend,hstartBank,hcost] at hret
  exact hret

/-- The prepared absent-marker cycle increments its bank and returns
silently through that bank to state 1 immediately left of the nearer pair. -/
theorem padded_absent_increment_return1_with_marker (a : Int) (r v : Nat) (rest : List Nat)
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
      silentSegment machine (cfg 93 a t) (cfg 1 (a+27) e.tape)
        ((((((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32))+28)+(r+6))+
          (v+3+(encode (rest ++ [0])).length))+
          ((encode ((v+1)::(rest ++ [0]))).length+(r+5)+2)) ∧
      Holds e.tape (a+36+(r : Int))
        ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) ∧
      e.tape (a-3)=false ∧ (∀ q, q<a+26 → e.tape q=t q) ∧
      e.tape (a+27)=false ∧ e.tape (a+28)=false ∧ e.tape (a+29)=false ∧
      Holds e.tape (a+30) (List.replicate (r+5) true ++ [false]) ∧
      e.tape (a+26)=true := by
  obtain ⟨mid,hs,hseg,hbank,_hmissing,hleft,hdelim⟩ :=
    padded_absent_exact_next14_with_delimiter a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  let t1 := setAt (a+29) (setAt (a+30) mid.tape)
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
  let selected := clearAt (a+28) output
  let base := a+36+(r : Int)
  let tail := rest ++ [0]
  have hbank' : Holds selected base ((encode (v::tail) ++ [false,false,false]) ++ suffix) := by
    simpa [base,tail] using hbank
  obtain ⟨e,he,hehead,hebank,heleft,heinc⟩ :=
    exact_increment_with_suffix v tail base suffix selected hbank'
  have hselectedRun : Holds selected (a+30) (List.replicate (r+5) true ++ [false]) :=
    selected_scan_word a r v rest t1 hdelim
  have herun : Holds e.tape (a+30) (List.replicate (r+5) true ++ [false]) := by
    apply holds_transport selected e.tape _ _ hselectedRun
    intro q _ hq
    symm
    apply heleft
    have hn : (List.replicate (r+5) true ++ [false]).length=r+6 := by simp
    rw [hn] at hq
    dsimp [base]
    omega
  have he0 : e.tape (a+28)=false := by
    rw [heleft _ (by dsimp [base]; omega)]
    simp [selected,clearAt]
  have he1 : e.tape (a+28+1)=false := by
    rw [heleft _ (by dsimp [base]; omega)]
    have hp : a+28+1=a+29 := by omega
    rw [hp]
    have hgap : final (a+29)=false := by
      apply return_carry_gap
      all_goals omega
    simpa [selected,clearAt,output,fillRange,setAt,final] using hgap
  have hebankSmall : Holds e.tape base (encode ((v+1)::tail)) := by
    apply holds_prefix_word e.tape base _ ([false,false] ++ suffix)
    simpa [List.append_assoc] using hebank
  have hreturn := bank_run_to1 (v+1) tail (a+28) (r+5) e.tape (by omega) he0 he1
    (by
      have hp : a+28+2=a+30 := by omega
      rw [hp]
      exact herun)
    (by have hp : a+28+2+((r+5 : Nat):Int)+1=base := by dsimp [base]; omega
        rw [hp]
        exact hebankSmall)
  have hehead' : e.head=base+((encode ((v+1)::tail)).length : Int)-2 := by
    rw [hehead]
    simp only [encode,List.length_append,block_length,Nat.cast_add]
    push_cast
    omega
  have hecfg : e=cfg 23 e.head e.tape := by
    have hh : e=cfg e.state e.head e.tape := by cases e; rfl
    simpa only [he] using hh
  have hp : a+28+2+((r+5 : Nat):Int)+1=base := by dsimp [base]; omega
  dsimp only at hreturn
  rw [hp,←hehead',←hecfg] at hreturn
  have hend : a+28-1=a+27 := by omega
  rw [hend] at hreturn
  have hall := segAdd machine _ _ _ _ (v+3+(encode tail).length) hseg heinc
  have hall' := segAdd machine _ _ _ _ ((encode ((v+1)::tail)).length+(r+5)+2) hall hreturn
  have hleft' : ∀ q, q<a+26 → e.tape q=t q := by
    intro q hq
    calc
      e.tape q = selected q := heleft q (by dsimp [base]; omega)
      _ = t q := hleft q hq
  have hmissing : e.tape (a-3)=false := (hleft' _ (by omega)).trans absent
  have he27 : e.tape (a+27)=false := by
    rw [heleft _ (by dsimp [base]; omega)]
    have hp : a+30-3=a+27 := by omega
    have hgap : final (a+27)=false := by
      simpa only [final,hp] using return_clears_after_marker (a+30) (r+3) (selectorOutput a r v rest t1)
    simpa [selected,clearAt,output,fillRange,setAt,final] using hgap
  have he29 : e.tape (a+29)=false := by
    have hp : a+28+1=a+29 := by omega
    simpa only [hp] using he1
  have he26 : e.tape (a+26)=true := by
    rw [heleft _ (by dsimp [base]; omega)]
    have hp : a+30-4=a+26 := by omega
    have hmark : final (a+26)=true := by
      simpa only [final,hp] using return_left_marker (a+30) (r+3) (selectorOutput a r v rest t1)
    simpa [selected,clearAt,output,fillRange,setAt,final] using hmark
  exact ⟨mid,e,hs,he,hall',by simpa [base,tail] using hebank,hmissing,hleft',he27,he0,he29,herun,he26⟩

/-- Retain the earlier control interface. -/
theorem padded_absent_increment_return1_with_control (a : Int) (r v : Nat) (rest : List Nat)
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
      silentSegment machine (cfg 93 a t) (cfg 1 (a+27) e.tape)
        ((((((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32))+28)+(r+6))+
          (v+3+(encode (rest ++ [0])).length))+
          ((encode ((v+1)::(rest ++ [0]))).length+(r+5)+2)) ∧
      Holds e.tape (a+36+(r : Int))
        ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) ∧
      e.tape (a-3)=false ∧ (∀ q, q<a+26 → e.tape q=t q) ∧
      e.tape (a+27)=false ∧ e.tape (a+28)=false ∧ e.tape (a+29)=false ∧
      Holds e.tape (a+30) (List.replicate (r+5) true ++ [false]) := by
  obtain ⟨mid,e,hs,he,hseg,hbank,hmissing,hleft,h27,h28,h29,hrun,_hmark⟩ :=
    padded_absent_increment_return1_with_marker a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  exact ⟨mid,e,hs,he,hseg,hbank,hmissing,hleft,h27,h28,h29,hrun⟩

/-- Retain the earlier return interface. -/
theorem padded_absent_increment_return1 (a : Int) (r v : Nat) (rest : List Nat)
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
      silentSegment machine (cfg 93 a t) (cfg 1 (a+27) e.tape)
        ((((((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32))+28)+(r+6))+
          (v+3+(encode (rest ++ [0])).length))+
          ((encode ((v+1)::(rest ++ [0]))).length+(r+5)+2)) ∧
      Holds e.tape (a+36+(r : Int))
        ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) ∧
      e.tape (a-3)=false ∧ (∀ q, q<a+26 → e.tape q=t q) := by
  obtain ⟨mid,e,hs,he,hseg,hbank,hmissing,hleft,_h27,_h28,_h29,_hrun⟩ :=
    padded_absent_increment_return1_with_control a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  exact ⟨mid,e,hs,he,hseg,hbank,hmissing,hleft⟩

#print axioms padded_absent_increment_return1_with_marker
#print axioms padded_absent_increment_return1_with_control
#print axioms padded_absent_increment_return1
#print axioms bank_run_to1
end Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
