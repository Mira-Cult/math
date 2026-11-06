import Shared.Beeping.NPcoNP.NativeAllZeroReturnWindow

/-! Continue the prepared marker-absent cycle through its next unit dispatch.
This does not assert blank-start reachability or graph refinement. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroNextUnit
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
open Shared.Beeping.NPcoNP.NativeAllZeroReturnWindow
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

/-- The next window selects the unit branch and reaches state 12 in 28
silent transitions, clearing only its indicated control cell. -/
theorem next_window_to12 (a : Int) (r : Nat) (t : Int → Bool)
    (window : Holds t (a+2) (markerWindow (List.replicate 11 0 ++ [1,0,r+2]))) :
    silentSegment machine (cfg 93 (a+2) t) (cfg 12 (a+30) (clearAt (a+28) t)) 28 := by
  have h := marker_unit_to12 t (a+2) 11 0 (r+2) [] (by simpa using window)
  dsimp only at h
  have hd : a+2+((2*11 : Nat):Int)+4=a+28 := by norm_num; omega
  have hp : a+2+((2*11 : Nat):Int)+4+((0 : Nat):Int)+2=a+30 := by norm_num; omega
  have hc : 2*11+0+6=28 := by decide
  have hp2 : a+28+((0 : Nat):Int)+2=a+30 := by omega
  simpa only [hd,hp,hp2,hc] using h

/-- The supplied padded absent-marker cycle reaches the next unit branch,
with its bank and protected left tape still present at state 12. -/
theorem padded_absent_next_unit (a : Int) (r v : Nat) (rest : List Nat)
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
      silentSegment machine (cfg 93 a t) (cfg 12 (a+30) selected)
        (((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32))+28) ∧
      Holds selected (a+36+(r : Int))
        ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → selected q=t q) := by
  obtain ⟨mid,hs,hseg,hwindow,_hmarker,hbank,hleft⟩ :=
    padded_absent_next93 a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  let t1 := setAt (a+29) (setAt (a+30) mid.tape)
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
  let selected := clearAt (a+28) output
  have hnext := next_window_to12 a r output hwindow
  have hall := segAdd machine _ _ _ _ 28 hseg hnext
  have hbank' : Holds selected (a+36+(r : Int))
      ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) := by
    apply holds_transport output selected _ _ hbank
    intro q hq _
    symm
    change (if q=a+28 then false else output q)=output q
    rw [if_neg (by omega)]
  have hleft' : ∀ q, q<a+26 → selected q=t q := by
    intro q hq
    calc
      selected q = output q := by
        change (if q=a+28 then false else output q)=output q
        rw [if_neg (by omega)]
      _ = t q := hleft q hq
  exact ⟨mid,hs,hall,hbank',hleft'⟩

#print axioms next_window_to12
#print axioms padded_absent_next_unit
end Shared.Beeping.NPcoNP.NativeAllZeroNextUnit
