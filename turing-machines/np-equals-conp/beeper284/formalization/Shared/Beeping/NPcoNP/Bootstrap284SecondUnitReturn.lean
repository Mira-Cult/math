import Shared.Beeping.NPcoNP.Bootstrap284SecondIncrementReturn
import Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
import Shared.Beeping.NPcoNP.NativeTerminalUnitSelector

/-! The actual blank-start unit selector after the second bank increment.
This finite prefix does not establish a graph/table refinement. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284SecondUnitReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeTerminalUnitSelector
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.Bootstrap284NextReturnExact
open Shared.Beeping.NPcoNP.Bootstrap284NextSelectorExact
open Shared.Beeping.NPcoNP.Bootstrap284SecondIncrementReturn
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000
attribute [local irreducible] machine

theorem unit_word_append : unitWord=zeroWord ++ [true] := by decide

/-- Recover the unit selector from the proved blank-start left frame. -/
theorem actual_unit_window (out : Int → Bool)
    (frame : ∀ q, q≤ -8 → out q=returnTape q) :
    Holds out (-36) unitWord ∧ out (-37)=true := by
  have hw0 : Holds returnTape (-36) zeroWord := by
    simpa [zeroWord,List.replicate_succ] using return_window.1
  have hw : Holds out (-36) zeroWord := by
    apply holds_transport returnTape out _ _ hw0
    intro q _ hq
    have hlen : zeroWord.length=28 := by decide
    rw [hlen] at hq
    exact (frame q (by omega)).symm
  have he : out (-8)=true := (frame _ (by omega)).trans return_window.2.2
  have ht : Holds out ((-36:Int)+(zeroWord.length : Int)) [true] := by
    simpa [Holds,show zeroWord.length=28 by decide] using he
  have hall := holds_append_intro out (-36) zeroWord [true] hw ht
  refine ⟨?_,(frame _ (by omega)).trans return_window.2.1⟩
  rw [unit_word_append]
  exact hall

/-- At transition 2,134,479 the literal blank-start machine has completed
the marked unit selector and zero-corridor fill, with no emitted events. -/
theorem blank_start_second_unit_return_with_exterior :
    ∃ e : Config 284, e.state=23 ∧ e.head=10 ∧
      let before := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
      let after := fillRange (setAt (-6) before) (-4) 3
      Holds before (-36) unitWord ∧ before (-37)=true ∧
      Holds after 5 (encode [1,0,0]) ∧
      before (-5)=false ∧ (∀ q, q≤ -8 → before q=returnTape q) ∧
      (∀ q, q<5 ∨ 10<q → e.tape q=inputTape q) ∧
      machine.system.run 2134479=cfg 83 1 after ∧
      silentSegment machine (machine.system.run 0) (cfg 83 1 after) 2134479 := by
  obtain ⟨e,hs,hh,hbank,h7,h6,h5,hframe,hext,_hrun,hseg⟩ := blank_start_second_near_carry_with_exterior
  let before := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
  let after := fillRange (setAt (-6) before) (-4) 3
  obtain ⟨hwindow,hmarker⟩ := actual_unit_window before hframe
  have hscan := marker_window_to93 before (-36) (List.replicate 13 0 ++ [1])
    (by decide) hwindow hmarker
  have hscan' : silentSegment machine (cfg 83 (-8) before) (cfg 93 (-36) before) 30 := by
    simpa [encode,block,List.replicate_succ] using hscan
  have hzero : ∀ i : Nat, i<7 → before (-4+(i : Int))=false := by
    intro i hi
    have hi' : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [before,put,clearRange]
  have hlast : before 3=true := by simp [before,put]
  have hunit := terminal_unit_fill_return before (-36) 13 7 (by omega) hwindow
    (by simpa using h7) (by simpa using h6) (by simpa using h5)
    (by simpa using hzero) (by simpa using hlast)
  have hunit' : silentSegment machine (cfg 93 (-36) before) (cfg 83 1 after) 41 := by
    simpa [after] using hunit
  have hbank' : Holds after 5 (encode [1,0,0]) := by
    apply holds_transport before after _ _ hbank
    intro q hq _
    symm
    simp [after,fillRange,setAt,show q≠(-6:Int) by omega,
      show ¬((-4:Int)≤q ∧ q<3) by omega]
  have hmid := segAdd machine _ _ _ 2134408 30 hseg hscan'
  have hall := segAdd machine _ _ _ (2134408+30) 41 hmid hunit'
  have hall' : silentSegment machine (machine.system.run 0) (cfg 83 1 after) 2134479 := by
    simpa using hall
  exact ⟨e,hs,hh,hwindow,hmarker,hbank',h5,hframe,hext,run_of_initial_segment 2134479 _ hall',hall'⟩

/-- Retain the earlier unit-return frame interface. -/
theorem blank_start_second_unit_return_with_frame :
    ∃ e : Config 284, e.state=23 ∧ e.head=10 ∧
      let before := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
      let after := fillRange (setAt (-6) before) (-4) 3
      Holds before (-36) unitWord ∧ before (-37)=true ∧
      Holds after 5 (encode [1,0,0]) ∧
      before (-5)=false ∧ (∀ q, q≤ -8 → before q=returnTape q) ∧
      machine.system.run 2134479=cfg 83 1 after ∧
      silentSegment machine (machine.system.run 0) (cfg 83 1 after) 2134479 := by
  obtain ⟨e,hs,hh,hw,hm,hbank,h5,hframe,_hext,hrun,hseg⟩ := blank_start_second_unit_return_with_exterior
  exact ⟨e,hs,hh,hw,hm,hbank,h5,hframe,hrun,hseg⟩

/-- Retain the original unit-return interface. -/
theorem blank_start_second_unit_return :
    ∃ e : Config 284, e.state=23 ∧ e.head=10 ∧
      let before := put (clearRange (put (put e.tape (-7) true) (-4) false) (-3) 4) 3 true
      let after := fillRange (setAt (-6) before) (-4) 3
      Holds before (-36) unitWord ∧ before (-37)=true ∧
      Holds after 5 (encode [1,0,0]) ∧
      machine.system.run 2134479=cfg 83 1 after ∧
      silentSegment machine (machine.system.run 0) (cfg 83 1 after) 2134479 := by
  obtain ⟨e,hs,hh,hw,hm,hbank,_h5,_hframe,hrun,hseg⟩ := blank_start_second_unit_return_with_frame
  exact ⟨e,hs,hh,hw,hm,hbank,hrun,hseg⟩

#print axioms actual_unit_window
#print axioms blank_start_second_unit_return
#print axioms blank_start_second_unit_return_with_frame
#print axioms blank_start_second_unit_return_with_exterior
end Shared.Beeping.NPcoNP.Bootstrap284SecondUnitReturn
