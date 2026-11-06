import Shared.Beeping.NPcoNP.NativeAllZeroActualBit

/-! Track the actual delimiter through the prepared padded selector cycle.
This is a local segment, not blank-start reachability or graph refinement. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroActualDelimiter
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeAllZeroPositiveCycle
open Shared.Beeping.NPcoNP.NativeAllZeroActualBit
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

/-- Determinism transports the terminal delimiter and scan bit to the
padded cycle's actual output, without constraining its arbitrary suffix. -/
theorem padded_cycle_with_actual_delimiter (a : Int) (r v : Nat) (rest : List Nat)
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
      final (a+35+(r : Int))=false ∧
      Holds final (a+36+(r : Int))
        ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → final q=t q) := by
  have hpref : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false,false,false]) :=
    holds_prefix_word t _ _ ([false,false] ++ suffix) bank
  obtain ⟨mid1,_hs1,hseg1,_hw1,_hb1,_hm1,_hbank1,_hl1,_hr1,_hcell,hdelim⟩ :=
    all_zero_positive_cycle_framed_with_bits a r v rest t window left0 earlier marker nextZero h0 h1 hz hm delimiter hpref
  obtain ⟨mid2,hs2,hseg2,hw2,hb2,hm2,hcell2,hbank2,hl2⟩ :=
    padded_cycle_with_actual_bit a r v rest suffix t window left0 earlier marker nextZero h0 h1 hz hm delimiter bank
  let t1 := setAt (a+29) (setAt (a+30) mid1.tape)
  let final1 := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  let t2 := setAt (a+29) (setAt (a+30) mid2.tape)
  let final2 := outTape (a+30) (r+3) (selectorOutput a r v rest t2)
  have hzero : final1 (a+35+(r : Int))=false := by
    change outTape (a+30) (r+3) (selectorOutput a r v rest t1) (a+35+(r : Int))=false
    rw [return_output_right (a+30) (r+3) _ _ (by omega) (by push_cast; omega)]
    unfold selectorOutput
    rw [spec_outside _ _ _ _ (Or.inl (by push_cast; omega))]
    change (if a+35+(r : Int)=a+30 then false else t1 (a+35+(r : Int)))=false
    rw [if_neg (by omega)]
    exact hdelim
  have hcfg : cfg 83 (a+25) final1=cfg 83 (a+25) final2 := hseg1.1.symm.trans hseg2.1
  have htapes : final1=final2 := congrArg Config.tape hcfg
  have hz2 : final2 (a+35+(r : Int))=false := by rw [← htapes]; exact hzero
  exact ⟨mid2,hs2,hseg2,hw2,hb2,hm2,hcell2,hz2,hbank2,hl2⟩

#print axioms padded_cycle_with_actual_delimiter
end Shared.Beeping.NPcoNP.NativeAllZeroActualDelimiter
