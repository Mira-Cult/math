import Shared.Beeping.NPcoNP.NativeAllZeroToUnit
import Shared.Beeping.NPcoNP.Bootstrap284SecondAllZeroExact

/-! Specialize the parameterized all-zero-to-unit segment to the actual
blank-start selector frame. This is a finite startup theorem. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284AllZeroToUnit
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeAllZeroToUnit
open Shared.Beeping.NPcoNP.Bootstrap284NextBankExact
open Shared.Beeping.NPcoNP.Bootstrap284NextReturnExact
open Shared.Beeping.NPcoNP.Bootstrap284NextSelectorExact
open Shared.Beeping.NPcoNP.Bootstrap284SecondAllZeroExact
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000
attribute [local irreducible] machine

/-- The unit dispatch does not create the earlier left marker needed by
the later terminal-return interface. That marker must already be supplied. -/
theorem previous_marker_preserved (a : Int) (r : Nat) (t : Int → Bool) :
    clearAt (a+30) (filled a r t) (a-1)=t (a-1) := by
  change (if a-1=a+30 then false else filled a r t (a-1))=t (a-1)
  rw [if_neg (by omega),filled_before a r t (a-1) (by omega)]

/-- The exact physical selector frame reached from blank start satisfies
the parameterized macro's hypotheses with run parameter five. -/
theorem actual_fill_to_unit :
    silentSegment machine (cfg 93 (-36) returnTape)
      (cfg 12 (-4) (clearAt (-6) afterZero)) 104 := by
  have hw : Holds returnTape (-36) (markerWindow (List.replicate 13 0 ++ [0])) := by
    simpa [List.replicate_succ] using return_window.1
  have hz : ∀ i : Nat, i<5+2 → returnTape (-36+32+(i : Int))=false := by
    intro i hi
    exact return_zeros _ (by omega) (by omega)
  have h := fill_to_unit (-36) 5 returnTape hw
    (by simpa using return_window.2.2)
    (by simpa using return_zeros (-7) (by omega) (by omega))
    (by simpa using return_zeros (-6) (by omega) (by omega))
    (by simpa using return_zeros (-5) (by omega) (by omega))
    hz (by simpa using return_one)
  simpa [filled,afterZero] using h

/-- The literal table reaches state 12 at exactly 2,134,352 transitions
from blank tape, with the entire preceding physical execution silent. -/
theorem blank_start_unit_dispatch_exact :
    machine.system.run 2134352=cfg 12 (-4) (clearAt (-6) afterZero) ∧
    silentSegment machine (machine.system.run 0)
      (cfg 12 (-4) (clearAt (-6) afterZero)) 2134352 := by
  have h := segAdd machine _ _ _ 2134248 104 blank_start_next_selector_exact.2.2.2.2
    actual_fill_to_unit
  exact ⟨run_of_initial_segment 2134352 _ h,h⟩

/-- The later unit dispatch retains every cell from the bank separator
onward, not only the finite bank word displayed below. -/
theorem unit_bank_frame (q : Int) (hq : 4≤q) :
    clearAt (-6) afterZero q=nextBankTape q := by
  change (if q = -6 then false else
    if -4≤q ∧ q<3 then true else
    if q = -6 then true else
    if q = 3 then true else
    if -1≤q ∧ q<4 then false else
    if q = -2 then false else
    if q = -8 then true else
    if -8<q ∧ q≤ -5 then false else nextBankTape q)=nextBankTape q
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

/-- The tape specified at the blank-start unit boundary has the earlier
marker required by the later terminal-return lemma. -/
theorem unit_tape_previous_marker :
    clearAt (-6) afterZero (-37)=true := by
  have h := previous_marker_preserved (-36) 5 returnTape
  have h' : clearAt (-6) afterZero (-37)=returnTape (-37) := by
    simpa [filled,afterZero] using h
  exact h'.trans return_window.2.1

/-- The checked bank word survives the selector and unit dispatch on the
actual blank-start run, including its explicit trailing cells. -/
theorem blank_start_unit_bank :
    Holds (machine.system.run 2134352).tape 5
      (encode [0,0] ++ [true,false,false]) := by
  have ht : Holds (cfg 12 (-4) (clearAt (-6) afterZero) : Config 284).tape 5
      (encode [0,0] ++ [true,false,false]) := by
    apply holds_transport nextBankTape _ 5 _ next_bank_segment.1
    intro q hq _
    exact (unit_bank_frame q (by omega)).symm
  exact (congrArg (fun c : Config 284 =>
    Holds c.tape 5 (encode [0,0] ++ [true,false,false]))
    blank_start_unit_dispatch_exact.1).mpr ht

#print axioms actual_fill_to_unit
#print axioms blank_start_unit_dispatch_exact
#print axioms previous_marker_preserved
#print axioms unit_tape_previous_marker
#print axioms blank_start_unit_bank
end Shared.Beeping.NPcoNP.Bootstrap284AllZeroToUnit
