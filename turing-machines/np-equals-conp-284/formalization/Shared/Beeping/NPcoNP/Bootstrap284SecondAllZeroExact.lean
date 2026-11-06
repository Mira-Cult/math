import Shared.Beeping.NPcoNP.Bootstrap284NextSelectorExact
import Shared.Beeping.NPcoNP.NativeAllZeroSelector

/-! Continue the actual blank-start selector through its next all-zero
dispatch, without assuming the selector layout or an event-free interval. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284SecondAllZeroExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeAllZeroSelector
open Shared.Beeping.NPcoNP.Bootstrap284NextReturnExact
open Shared.Beeping.NPcoNP.Bootstrap284NextSelectorExact
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

def afterZero : Int → Bool := fillRange (setAt (-6) returnTape) (-4) 3

theorem return_zeros (q : Int) (hl : -8<q) (hr : q<3) : returnTape q=false := by
  by_cases hb : q< -1
  · have hh := scan28_cells.2.1 q hl hb
    simpa [returnTape,put,clearRange,show q≠3 by omega,
      show ¬((-1:Int)≤q ∧ q<4) by omega] using hh
  · simp [returnTape,put,clearRange,show q≠3 by omega,
      show (-1:Int)≤q ∧ q<4 by omega]

theorem return_one : returnTape 3=true := by simp [returnTape,put]

/-- The actual next all-zero selector and fill take 41 silent transitions
and specify the entire output tape. -/
theorem second_all_zero_segment :
    silentSegment machine (cfg 93 (-36) returnTape) (cfg 83 1 afterZero) 41 := by
  have hw : Holds returnTape (-36) (markerWindow (List.replicate 13 0 ++ [0])) := by
    simpa [List.replicate_succ] using return_window.1
  have hz : ∀ i : Nat, i<7 → returnTape (-4+(i : Int))=false := by
    intro i hi
    exact return_zeros _ (by omega) (by omega)
  have hs := all_zero_fill_return returnTape (-36) 13 7 (by decide) hw
    (by simpa using return_window.2.2)
    (by simpa using return_zeros (-7) (by omega) (by omega))
    (by simpa using return_zeros (-6) (by omega) (by omega))
    (by simpa using return_zeros (-5) (by omega) (by omega))
    (by simpa using hz) (by simpa using return_one)
  simpa [afterZero] using hs

/-- The stated complete tape is reached from blank start at the exact time,
with no flagged transitions in the whole prefix. -/
theorem blank_start_second_all_zero_exact :
    machine.system.run 2134289=cfg 83 1 afterZero ∧
    silentSegment machine (machine.system.run 0) (cfg 83 1 afterZero) 2134289 := by
  have hs := segAdd machine _ _ _ 2134248 41 blank_start_next_selector_exact.2.2.2.2
    second_all_zero_segment
  exact ⟨run_of_initial_segment 2134289 _ hs,hs⟩

#print axioms blank_start_second_all_zero_exact
end Shared.Beeping.NPcoNP.Bootstrap284SecondAllZeroExact
