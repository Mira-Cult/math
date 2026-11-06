import Shared.Beeping.NPcoNP.Bootstrap284FirstExit
import Shared.Beeping.NPcoNP.NativeHalfSelectorReturn

/-! Kernel-checked literal transitions following the recorded bootstrap,
and their connection to the existing state-97 marker progress theorem.
These are finite-run statements, not an infinite-run refinement. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284State97

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284BulkContinue7665
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.Bootstrap284FirstExit

set_option maxRecDepth 131072
set_option maxHeartbeats 12000000

def after28 : Packed :=
  (runSilent (-4096) 4104 28 output7665).getD ⟨0,0,0⟩

theorem checked28 : runSilent (-4096) 4104 28 output7665 = some after28 := by decide

theorem segment28 : silentSegment machine (toConfig (-4096) 4104 output7665)
    (toConfig (-4096) 4104 after28) 28 :=
  runSilent_sound (-4096) 4104 28 output7665 after28 checked28

theorem blank_start_28 : silentSegment machine (machine.system.run 0)
    (toConfig (-4096) 4104 after28) 2133520 := by
  have h := segAdd machine _ _ _ 2133492 28 blank_start_7665 segment28
  simpa using h

theorem run_2133520 : machine.system.run 2133520 = toConfig (-4096) 4104 after28 :=
  run_of_initial_segment 2133520 _ blank_start_28

theorem state97 : (machine.system.run 2133520).state=97 := by
  rw [run_2133520]
  decide

theorem head2 : (machine.system.run 2133520).head=2 := by
  rw [run_2133520]
  decide

theorem marker_neg4 : (machine.system.run 2133520).tape (-4)=true := by
  rw [run_2133520]
  decide

/-- The exact checked continuation supplies the leftward marker needed to
reach state 93 through positive finite silent execution. -/
theorem blank_start_through_state93 :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=93 ∧
      silentSegment machine (machine.system.run 0) e (2133520+n) := by
  have hp : (-4 : Int) ≤ (machine.system.run 2133520).head := by rw [head2]; omega
  obtain ⟨n,e,hn,he,_,hseg⟩ :=
    reachable_97_to_93 2133520 state97 (-4) hp marker_neg4
  refine ⟨n,e,hn,he,?_⟩
  apply segAdd machine _ _ _ 2133520 n blank_start_28
  rw [← run_2133520]
  exact hseg

end Shared.Beeping.NPcoNP.Bootstrap284State97

#print axioms Shared.Beeping.NPcoNP.Bootstrap284State97.blank_start_through_state93
