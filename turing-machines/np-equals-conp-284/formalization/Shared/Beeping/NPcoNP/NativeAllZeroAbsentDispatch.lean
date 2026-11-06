import Shared.Beeping.NPcoNP.NativeAllZeroCycleDispatch
import Shared.Beeping.NPcoNP.NativeAllZeroCyclePadding

/-! The marker-absent branch of the prepared all-zero selector cycle.
The segment is local: it does not establish blank-start reachability or
the behavior of the new control window after state 93 is reached. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroAbsentDispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeAllZeroCyclePadding
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

/-- The carry-and-return tape effect clears the cell just after the new
marker. This pointwise fact requires no assumption on the rest of the tape. -/
theorem return_clears_after_marker (d : Int) (r : Nat) (t : Int → Bool) :
    outTape d r t (d-3)=false := by
  unfold outTape clearRange scanTape carryTape result cleared put
  simp only
  have h0 : d-3 ≠ d+1+(r : Int) := by omega
  have h1 : ¬ (d+3 ≤ d-3 ∧ d-3 < d+2+(r : Int)) := by omega
  have h2 : d-3 ≠ d+2 := by omega
  have h3 : d-3 ≠ (d-1)-(3 : Int) := by omega
  have h4 : (d-1)-(3 : Int) < d-3 ∧ d-3 ≤ d-1 := by omega
  simp [h0,h1,h2,h3,h4]

/-- A supplied all-zero window with an absent earlier marker returns to
state 93 at the old anchor, without a beep or a tape change. -/
theorem marker_absent_dispatch (a : Int) (t : Int → Bool)
    (window : Holds t (a-2) (markerWindow (List.replicate 13 0 ++ [0])))
    (marker : t (a-3)=false) :
    silentSegment machine (cfg 83 (a+25) t) (cfg 93 a t) 31 := by
  let xs := List.replicate 13 0 ++ [0]
  have hlen : (encode xs).length=28 := by decide
  have hs := marker_window_to92 t (a-2) xs (by simp [xs]) window
  rw [hlen] at hs
  have hp : a-2+((28 : Nat):Int)-1=a+25 := by omega
  rw [hp, show a-2-1=a-3 by omega] at hs
  have h0 : t (a-2)=false := by
    have h := holds_get t (a-2) (markerWindow xs) window 0 (by decide)
    have hb : (markerWindow xs)[0]=false := by decide
    rw [hb] at h
    simpa using h
  have h1 : t (a-1)=true := by
    have h := holds_get t (a-2) (markerWindow xs) window 1 (by decide)
    have hb : (markerWindow xs)[1]=true := by decide
    rw [hb] at h
    have hp1 : a-2+(1:Int)=a-1 := by omega
    simpa [hp1] using h
  have hfirst : silentSegment machine (cfg 92 (a-3) t) (cfg 92 (a-2) t) 1 := by
    simpa only [show a-3+1=a-2 by omega] using oneSeg machine _ _ (step92_zero (a-3) t marker)
  have hsecond : silentSegment machine (cfg 92 (a-2) t) (cfg 92 (a-1) t) 1 := by
    simpa only [show a-2+1=a-1 by omega] using oneSeg machine _ _ (step92_zero (a-2) t h0)
  have hthird : silentSegment machine (cfg 92 (a-1) t) (cfg 93 a t) 1 := by
    simpa only [show a-1+1=a by omega] using oneSeg machine _ _ (step92_one (a-1) t h1)
  have h12 := segAdd machine _ _ _ 1 1 hfirst hsecond
  have h123 := segAdd machine _ _ _ 2 1 h12 hthird
  have hall := segAdd machine _ _ _ 28 3 hs h123
  simpa using hall

theorem absent_window_shape :
    (markerWindow (List.replicate 13 0 ++ [0])).drop 2 ++ [true,false] =
      (List.replicate 13 [false,true]).flatten ++ [true,false] := by decide

theorem absent_window_ne_all_zero :
    (markerWindow (List.replicate 13 0 ++ [0])).drop 2 ++ [true,false] ≠
      markerWindow (List.replicate 13 0 ++ [0]) := by decide

/-- With the earlier marker absent, the padded local cycle reaches state 93
at the old anchor after 31 further silent steps. Its new 28-cell control
window ends in `10`; it is not the original all-zero window. -/
theorem all_zero_padded_absent_dispatch (a : Int) (r v : Nat) (rest : List Nat)
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
      silentSegment machine (cfg 93 a t) (cfg 93 a final)
        ((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31) ∧
      Holds final a ((markerWindow (List.replicate 13 0 ++ [0])).drop 2 ++ [true,false]) ∧
      Holds final (a+36+(r : Int))
        ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → final q=t q) := by
  obtain ⟨mid,hs,hseg,hwindow,hbefore,hmarker,hbank,hleft⟩ :=
    all_zero_cycle_padded a r v rest suffix t window left0 earlier marker nextZero h0 h1 hz hm delimiter bank
  let t1 := setAt (a+29) (setAt (a+30) mid.tape)
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  have habsent : final (a-3)=false := hbefore.trans absent
  have hdispatch := marker_absent_dispatch a final hwindow habsent
  have hall := segAdd machine _ _ _
    (((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
      ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
      ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18))) 31 hseg hdispatch
  let word := markerWindow (List.replicate 13 0 ++ [0])
  have hsplit : word = [false,true] ++ word.drop 2 := by decide
  have hdrop : Holds final a (word.drop 2) := by
    have hw : Holds final (a-2) word := hwindow
    rw [hsplit] at hw
    have h := holds_append_tail final (a-2) [false,true] (word.drop 2) hw
    simpa using h
  have hlen : (word.drop 2).length=26 := by decide
  have hz : final (a+27)=false := by
    have he : a+30-3=a+27 := by omega
    simpa only [final, he] using return_clears_after_marker (a+30) (r+3) (selectorOutput a r v rest t1)
  have hend : Holds final (a+26) [true,false] := by
    simp only [Holds]
    exact ⟨hmarker, by simpa only [show a+26+1=a+27 by omega] using hz, trivial⟩
  have hnew := holds_append_intro final a (word.drop 2) [true,false] hdrop (by simpa [hlen] using hend)
  exact ⟨mid,hs,hall,hnew,hbank,hleft⟩

#print axioms absent_window_shape
#print axioms absent_window_ne_all_zero
#print axioms return_clears_after_marker
#print axioms marker_absent_dispatch
#print axioms all_zero_padded_absent_dispatch
end Shared.Beeping.NPcoNP.NativeAllZeroAbsentDispatch
