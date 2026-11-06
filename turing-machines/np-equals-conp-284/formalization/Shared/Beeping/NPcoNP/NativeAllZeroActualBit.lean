import Shared.Beeping.NPcoNP.NativeAllZeroAbsentExact
import Shared.Beeping.NPcoNP.NativeAllZeroCyclePadding

/-! Establish the intermediate cell needed to select the exact long return.
All statements are for supplied prepared layouts, not blank-start reachability. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroActualBit
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentDispatch
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentTo261
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentExact
open Shared.Beeping.NPcoNP.NativeAllZeroPositiveCycle
open Shared.Beeping.NPcoNP.NativeAllZeroCyclePadding
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

/-- A positive return's one-cell-right position is untouched. -/
theorem return_at_succ (d : Int) (r : Nat) (t : Int → Bool) (hr : 0<r) :
    outTape d r t (d+1)=t (d+1) := by
  unfold outTape clearRange scanTape carryTape result cleared put
  simp only
  have h0 : d+1≠d+1+(r : Int) := by omega
  have h1 : d+1≠d+2 := by omega
  have h2 : d+1≠(d-1)-(3 : Int) := by omega
  simp [h0,h1,h2]

/-- The actual cycle output has the zero needed for the long state-261
return. Deterministic execution identifies it with the padded output. -/
theorem padded_cycle_with_actual_bit (a : Int) (r v : Nat) (rest : List Nat)
    (suffix : List Bool) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
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
      silentSegment machine (cfg 93 a t) (cfg 83 (a+25) final)
        (((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18))) ∧
      Holds final (a-2) (markerWindow (List.replicate 13 0 ++ [0])) ∧
      final (a-3)=t (a-3) ∧ final (a+26)=true ∧ final (a+31)=false ∧
      Holds final (a+36+(r : Int))
        ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → final q=t q) := by
  have hpref : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false,false,false]) :=
    holds_prefix_word t _ _ ([false,false] ++ suffix) bank
  obtain ⟨mid1,_hs1,hseg1,_hw1,_hb1,_hm1,_hbank1,_hl1,_hr1,hcell⟩ :=
    all_zero_positive_cycle_framed_with_bit a r v rest t window left0 earlier marker nextZero h0 h1 hz hm delimiter hpref
  obtain ⟨mid2,hs2,hseg2,hw2,hb2,hm2,hbank2,hl2⟩ :=
    all_zero_cycle_padded a r v rest suffix t window left0 earlier marker nextZero h0 h1 hz hm delimiter bank
  let t1 := setAt (a+29) (setAt (a+30) mid1.tape)
  let final1 := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  let t2 := setAt (a+29) (setAt (a+30) mid2.tape)
  let final2 := outTape (a+30) (r+3) (selectorOutput a r v rest t2)
  have hzero : final1 (a+31)=false := by
    have hp : a+30+1=a+31 := by omega
    rw [← hp]
    change outTape (a+30) (r+3) (selectorOutput a r v rest t1) (a+30+1)=false
    rw [return_at_succ _ _ _ (by omega)]
    unfold selectorOutput
    rw [spec_outside _ _ _ _ (Or.inl (by push_cast; omega))]
    simp [clearAt,hcell,t1,hp]
  have hcfg : cfg 83 (a+25) final1 = cfg 83 (a+25) final2 := hseg1.1.symm.trans hseg2.1
  have htapes : final1=final2 := congrArg Config.tape hcfg
  have hz2 : final2 (a+31)=false := by rw [← htapes]; exact hzero
  exact ⟨mid2,hs2,hseg2,hw2,hb2,hm2,hz2,hbank2,hl2⟩

/-- The marker-absent prepared cycle takes the long return branch. Its
explicit state-83 tape still contains the extended bank and agrees with the
initial tape on the protected left. -/
theorem padded_absent_long_return (a : Int) (r v : Nat) (rest : List Nat)
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
      silentSegment machine (cfg 93 a t) (cfg 83 (a+32+(r : Int)) output)
        (((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8)) ∧
      Holds output (a+36+(r : Int))
        ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → output q=t q) := by
  obtain ⟨mid,hs,hseg,hwindow,hbefore,hmarker,hbit,hbank,hleft⟩ :=
    padded_cycle_with_actual_bit a r v rest suffix t window left0 earlier marker nextZero h0 h1 hz hm delimiter bank
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
  exact ⟨mid,hs,hall'',hbankout,hleftout⟩

#print axioms padded_absent_long_return
#print axioms return_at_succ
#print axioms padded_cycle_with_actual_bit
end Shared.Beeping.NPcoNP.NativeAllZeroActualBit
