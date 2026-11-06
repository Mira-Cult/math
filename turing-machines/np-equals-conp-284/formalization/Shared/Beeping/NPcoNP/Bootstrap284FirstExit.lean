import Shared.Beeping.NPcoNP.Bootstrap284RunBridge
import Shared.Beeping.NPcoNP.Bootstrap284BulkContinue7665
import Shared.Beeping.NPcoNP.NativeHalfState14Cycle
import Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport

/-! Checked blank-start bootstrap exit, connected to positive physical
progress through the state-261 one-branch. This is a finite segment, not a
proof of eventual silence or of graph refinement. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284FirstExit

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState14Cycle
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284RunBridge
open Shared.Beeping.NPcoNP.Bootstrap284BulkContinue7665

set_option maxRecDepth 131072
set_option maxHeartbeats 12000000

theorem run_first_exit : machine.system.run 2133492 = toConfig (-4096) 4104 output7665 :=
  run_of_initial_segment 2133492 _ blank_start_7665

theorem first_exit_state : (machine.system.run 2133492).state = 261 := by
  rw [run_first_exit]
  rfl

theorem first_exit_head : (machine.system.run 2133492).head = -2 := by
  rw [run_first_exit]
  rfl

theorem first_exit_reads_one :
    (machine.system.run 2133492).tape (machine.system.run 2133492).head = true := by
  rw [run_first_exit]
  decide

/-- The checked blank-start run continues beyond the exact bootstrap exit
to state 22 in positive finite time, without an intervening beep. -/
theorem first_exit_to_state22 :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=22 ∧
      silentSegment machine (machine.system.run 2133492) e n :=
  reachable_261_one_to_22 2133492 first_exit_state first_exit_reads_one

/-- Compose the exact paid bootstrap and its proved positive continuation. -/
theorem blank_start_through_state22 :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=22 ∧
      silentSegment machine (machine.system.run 0) e (2133492+n) := by
  obtain ⟨n,e,hn,he,hseg⟩ := first_exit_to_state22
  refine ⟨n,e,hn,he,?_⟩
  apply segAdd machine _ _ _ 2133492 n blank_start_7665
  rw [← run_first_exit]
  exact hseg

/-- The blank-start run also exits the following 14/22 loop: the loop's
positive finite duration is proved from finite tape support. -/
theorem blank_start_through_state23 :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=23 ∧
      silentSegment machine (machine.system.run 0) e (2133492+n) := by
  obtain ⟨n,e,hn,he,hseg⟩ :=
    reachable_261_one_to_23 2133492 first_exit_state first_exit_reads_one
  refine ⟨n,e,hn,he,?_⟩
  apply segAdd machine _ _ _ 2133492 n blank_start_7665
  rw [← run_first_exit]
  exact hseg

/-- Composing the existing left-zero return theorem proves that the
blank-start machine reaches state 1 after another finite silent segment. -/
theorem blank_start_through_state1 :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=1 ∧
      silentSegment machine (machine.system.run 0) e (2133492+n) := by
  obtain ⟨n,e,hn,he,hseg⟩ := blank_start_through_state23
  have hrun : machine.system.run (2133492+n)=e :=
    run_of_initial_segment (2133492+n) e hseg
  have hstate : (machine.system.run (2133492+n)).state=23 := by rw [hrun]; exact he
  obtain ⟨m,p,hm,hmore⟩ := reachable_23_progress (2133492+n) hstate
  refine ⟨n+m,cfg 1 p (machine.system.run (2133492+n)).tape,by omega,rfl,?_⟩
  have htail : silentSegment machine e
      (cfg 1 p (machine.system.run (2133492+n)).tape) m := by
    rw [← hrun]
    exact hmore
  have hall := segAdd machine _ _ _ (2133492+n) m hseg htail
  simpa [Nat.add_assoc] using hall

end Shared.Beeping.NPcoNP.Bootstrap284FirstExit

#print axioms Shared.Beeping.NPcoNP.Bootstrap284FirstExit.blank_start_through_state22
#print axioms Shared.Beeping.NPcoNP.Bootstrap284FirstExit.blank_start_through_state23
#print axioms Shared.Beeping.NPcoNP.Bootstrap284FirstExit.blank_start_through_state1
