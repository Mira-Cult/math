import Shared.Beeping.NPcoNP.NativeAllZeroPositiveCycle

/-! Continue a proved all-zero cycle to the next state-93 dispatch when
the preserved earlier marker is present. The false-marker branch is separate. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroCycleDispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeAllZeroPositiveCycle
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

/-- A supplied marked all-zero window is scanned in 29 silent transitions. -/
theorem marker_present_dispatch (a : Int) (t : Int → Bool)
    (window : Holds t (a-2) (markerWindow (List.replicate 13 0 ++ [0])))
    (marker : t (a-3)=true) :
    silentSegment machine (cfg 83 (a+25) t) (cfg 93 (a-2) t) 29 := by
  have h := marker_window_to93 t (a-2) (List.replicate 13 0 ++ [0]) (by simp)
    window (by
      have hp : a-2-1=a-3 := by omega
      rw [hp]
      exact marker)
  have hlen : (encode (List.replicate 13 0 ++ [0])).length=28 := by decide
  rw [hlen] at h
  have hp : a-2+((28 : Nat):Int)-1=a+25 := by omega
  have hc : 28+1=29 := by decide
  rw [hp,hc] at h
  exact h

/-- If the next earlier marker was already present, the full local cycle
continues to the next state-93 selector in explicitly charged silent time. -/
theorem all_zero_positive_dispatch (a : Int) (r v : Nat) (rest : List Nat)
    (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (nextMarker : t (a-3)=true)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false,false,false])) :
    ∃ mid : Config 284, mid.state=23 ∧
      let t1 := setAt (a+29) (setAt (a+30) mid.tape)
      let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
      silentSegment machine (cfg 93 a t) (cfg 93 (a-2) final)
        ((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+29) ∧
      Holds final (a-2) (markerWindow (List.replicate 13 0 ++ [0])) ∧
      final (a-3)=true ∧ final (a+26)=true ∧
      Holds final (a+36+(r : Int)) (encode (v::rest) ++ [true,false,false]) ∧
      (∀ q, q<a+26 → final q=t q) := by
  obtain ⟨mid,hs,hseg,hwindow,hbefore,hmark,hbank,hframe⟩ :=
    all_zero_positive_cycle a r v rest t window left0 earlier marker nextZero h0 h1 hz hm delimiter bank
  let t1 := setAt (a+29) (setAt (a+30) mid.tape)
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  have hmarker : final (a-3)=true := hbefore.trans nextMarker
  have hdispatch := marker_present_dispatch a final hwindow hmarker
  have hall := segAdd machine _ _ _
    (((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
      ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
      ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18))) 29 hseg hdispatch
  exact ⟨mid,hs,hall,hwindow,hmarker,hmark,hbank,hframe⟩

#print axioms marker_present_dispatch
#print axioms all_zero_positive_dispatch
end Shared.Beeping.NPcoNP.NativeAllZeroCycleDispatch
