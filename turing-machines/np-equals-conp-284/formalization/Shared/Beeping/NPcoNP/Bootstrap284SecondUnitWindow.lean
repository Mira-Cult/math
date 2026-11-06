import Shared.Beeping.NPcoNP.Bootstrap284SecondUnitReturn
import Shared.Beeping.NPcoNP.NativeAllZeroUnitWindow

/-! Identify the next selector on the actual blank-start run. This is a
finite physical prefix, not a graph refinement. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284SecondUnitWindow
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroNearCarry
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeAllZeroUnitScan
open Shared.Beeping.NPcoNP.NativeAllZeroUnitWindow
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.Bootstrap284NextReturnExact
open Shared.Beeping.NPcoNP.Bootstrap284NextSelectorExact
open Shared.Beeping.NPcoNP.Bootstrap284SecondUnitReturn
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000
attribute [local irreducible] machine

/-- An auxiliary tape completes the protected 26-cell prefix into an
all-zero word. It is only used to apply the general window lemma. -/
def prefixCompletion : Int → Bool := put (put returnTape (-8) false) (-7) true

theorem prefix_completion_window : Holds prefixCompletion (-34) zeroWord := by
  have hw : Holds returnTape (-36) zeroWord := by
    simpa [zeroWord,List.replicate_succ] using return_window.1
  have hsplit : zeroWord=[false,true] ++ zeroWord.take 26 := by decide
  rw [hsplit] at hw
  have ht := holds_append_tail returnTape (-36) [false,true] (zeroWord.take 26) hw
  have hprefix : Holds prefixCompletion (-34) (zeroWord.take 26) := by
    apply holds_transport returnTape prefixCompletion _ _ (by simpa using ht)
    intro q _ hq
    have hl : (zeroWord.take 26).length=26 := by decide
    rw [hl] at hq
    simp [prefixCompletion,put,show q≠(-7:Int) by omega,show q≠(-8:Int) by omega]
  have htail : Holds prefixCompletion (-8) [false,true] := by
    simp [prefixCompletion,put,Holds]
  have hall := holds_append_intro prefixCompletion (-34) (zeroWord.take 26) [false,true] hprefix (by
    have hp : (-34:Int)+((zeroWord.take 26).length : Int)= -8 := by decide
    rw [hp]
    exact htail)
  have he : zeroWord.take 26 ++ [false,true]=zeroWord := by decide
  simpa only [he] using hall

/-- The next actual selector is twelve zero values followed by three and
five, with its left marker present. -/
theorem actual_next_window (e : Config 284)
    (h5 : (put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true) (-5)=false)
    (frame : ∀ q, q≤ -8 →
      (put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true) q=returnTape q) :
    let before := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
    let after := fillRange (setAt (-6) before) (-4) 3
    Holds after (-34) (markerWindow (List.replicate 12 0 ++ [3,5])) ∧ after (-35)=true := by
  let before := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
  let after := fillRange (setAt (-6) before) (-4) 3
  have h26 : e.tape (-8)=true := by
    have hf := near_carry_frame (-34) 3 e.tape (-8) (Or.inl (by omega))
    have hb : before (-8)=true := (frame _ (by omega)).trans return_window.2.2
    exact (by simpa [before] using hf.symm.trans hb)
  have h29 : e.tape (-5)=false := by
    have hf : before (-5)=e.tape (-5) := by simp [before,put,clearRange]
    exact hf.symm.trans h5
  have hframe : ∀ q, q<(-34:Int)+26 → after q=prefixCompletion q := by
    intro q hq
    have hf : after q=returnTape q := by
      have hb : before q=returnTape q := frame q (by omega)
      simpa [after,fillRange,setAt,show q≠(-6:Int) by omega,
        show ¬((-4:Int)≤q ∧ q<3) by omega] using hb
    simpa [prefixCompletion,put,show q≠(-7:Int) by omega,show q≠(-8:Int) by omega] using hf
  have hw := unit_scan_window (-34) 3 prefixCompletion e.tape prefix_completion_window
    (by simpa using h26) (by simpa using h29) (by simpa [after,before,carryOutput] using hframe)
  have hm : after (-35)=true := by
    have hh := holds_get returnTape (-36) _ return_window.1 1 (by decide)
    have hv : (markerWindow (List.replicate 14 0))[1]=true := by decide
    rw [hv] at hh
    have hr : returnTape (-35)=true := by simpa using hh
    have hb : before (-35)=true := (frame _ (by omega)).trans hr
    simpa [after,fillRange,setAt] using hb
  exact ⟨by simpa [after,before,carryOutput] using hw,hm⟩

/-- This selector dispatches silently to state 93 at head -34 after 37
more transitions from the state-83 boundary. -/
theorem blank_start_second_unit_next93 :
    ∃ e : Config 284, e.state=23 ∧ e.head=10 ∧
      let before := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
      let after := fillRange (setAt (-6) before) (-4) 3
      Holds after (-34) (markerWindow (List.replicate 12 0 ++ [3,5])) ∧
      Holds after 5 (encode [1,0,0]) ∧
      machine.system.run 2134516=cfg 93 (-34) after ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-34) after) 2134516 := by
  obtain ⟨e,hs,hh,_hw,_hm,hbank,h5,hframe,_hrun,hseg⟩ := blank_start_second_unit_return_with_frame
  let before := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
  let after := fillRange (setAt (-6) before) (-4) 3
  obtain ⟨hwindow,hmarker⟩ := actual_next_window e h5 hframe
  have hnext := unit_scan_window_to93 (-34) 3 after (by simpa using hwindow) (by simpa using hmarker)
  have hnext' : silentSegment machine (cfg 83 1 after) (cfg 93 (-34) after) 37 := by
    simpa using hnext
  have hall := segAdd machine _ _ _ 2134479 37 hseg hnext'
  have hall' : silentSegment machine (machine.system.run 0) (cfg 93 (-34) after) 2134516 := by
    simpa using hall
  exact ⟨e,hs,hh,hwindow,hbank,run_of_initial_segment 2134516 _ hall',hall'⟩

#print axioms prefix_completion_window
#print axioms actual_next_window
#print axioms blank_start_second_unit_next93
end Shared.Beeping.NPcoNP.Bootstrap284SecondUnitWindow
