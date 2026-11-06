import Shared.Beeping.NPcoNP.NativeUnitCarryExact83
import Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn

/-! Remove the formerly existential carry duration in the checked startup. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284TerminalExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeUnitCarryExact83
open Shared.Beeping.NPcoNP.Bootstrap284Unit261Return
open Shared.Beeping.NPcoNP.Bootstrap284Unit261Actual83
open Shared.Beeping.NPcoNP.Bootstrap284TerminalUnit
open Shared.Beeping.NPcoNP.Bootstrap284ManyShift
open Shared.Beeping.NPcoNP.Bootstrap284ManyCarry
open Shared.Beeping.NPcoNP.Bootstrap284NextSelector
open Shared.Beeping.NPcoNP.Bootstrap284AllZeroReturn
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 12000000

/-- The state-1 carry at the checked seed takes exactly 15 silent steps. -/
theorem carry4_exact : silentSegment machine (cfg 1 (-3) postIncrement)
    (cfg 83 (-4) postCarry) 15 := by
  have h := carry_to83_exact 4 (-2) postIncrement (by decide)
    (by simpa using postIncrement_pre) postIncrement_h0 (by simpa using postIncrement_h1)
    (by simpa using postIncrement_scan)
  simpa [postCarry,carry4Tape] using h

/-- The earlier terminal-selector seed is reached after exactly 2,133,751
silent transitions from blank tape. -/
theorem blank_start_terminal_return_exact :
    silentSegment machine (machine.system.run 0) (cfg 83 1 postReturn) 2133751 := by
  have hfirst := segAdd machine _ _ _ 2133669 15 blank_start_unit_return1 carry4_exact
  have hall := segAdd machine _ _ _ (2133669+15) 67 hfirst checked_terminal_cycle
  exact hall

/-- The all-zero selector return previously reached with an existential carry
is reached at an exact blank-start time. -/
theorem blank_start_all_zero_return_exact :
    silentSegment machine (machine.system.run 0) (cfg 83 1 afterAllZero) 2133925 := by
  have h1 := segAdd machine _ _ _ 2133751 76 blank_start_terminal_return_exact checked_many_shift
  have h2 := segAdd machine _ _ _ (2133751+76) 6 h1 checked_return_to_carry
  have h3 := segAdd machine _ _ _ (2133751+76+6) 4 h2 checked_carry_to27
  have h3' : silentSegment machine (machine.system.run 0) (cfg 27 (-5) carryTape) 2133837 := by
    simpa [carryTape] using h3
  have h4 := segAdd machine _ _ _ 2133837 20 h3' exact_next_return
  have hs := marker_window_to93 nextTape (-34) (List.replicate 14 0)
    (by simp) nextTape_window.2.2 nextTape_window.2.1
  have hs' : silentSegment machine (cfg 83 (-7) nextTape) (cfg 93 (-34) nextTape) 29 := by
    simpa [encode,block,List.replicate_succ] using hs
  have h5 := segAdd machine _ _ _ (2133837+20) 29 h4 hs'
  have h6 := segAdd machine _ _ _ (2133837+20+29) 39 h5 all_zero_return
  exact h6

#print axioms carry4_exact
#print axioms blank_start_terminal_return_exact
#print axioms blank_start_all_zero_return_exact
end Shared.Beeping.NPcoNP.Bootstrap284TerminalExact
