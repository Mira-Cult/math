import Shared.Beeping.NPcoNP.Bootstrap284BulkContinue7424
import Shared.Beeping.NPcoNP.NativeHalfState14Progress

/-! Relate exact positive-segment certificates to the run indexing used by
the physical progress theorems. This is not an infinite-run refinement. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284RunBridge

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep

theorem run_of_initial_segment (time : Nat) (c : Config 284)
    (h : silentSegment machine (machine.system.run 0) c time) :
    machine.system.run time = c := by
  have ha : machine.system.advance (machine.system.run 0) time = c := by
    simpa only [W, ScalarWordRefinement.advance_ofBeep] using h.1
  simpa only [Nat.zero_add] using (EventSystem.run_add machine.system 0 time).trans ha

theorem run_7424 : machine.system.run 1958152 =
    toConfig (-4096) 4104 Bootstrap284BulkContinue7424.output7424 :=
  run_of_initial_segment 1958152 _ Bootstrap284BulkContinue7424.blank_start_7424

end Shared.Beeping.NPcoNP.Bootstrap284RunBridge

#print axioms Shared.Beeping.NPcoNP.Bootstrap284RunBridge.run_7424
