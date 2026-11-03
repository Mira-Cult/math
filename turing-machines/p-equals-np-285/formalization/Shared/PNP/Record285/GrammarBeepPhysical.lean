import Shared.PNP.Record285.GrammarBeep

/-! Physical marked-event transfer for a clean beep path. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
attribute [local irreducible] Record285.machine

theorem numeric_marked_left_step (M : Machine 285) (q p : Fin 285)
    (row : M.table.row q true = ⟨false,.left,p,true⟩)
    (head : Int) (left right : Nat) :
    PhysicalNumeric.step M ⟨q,head,left,true,right⟩ =
      (⟨p,head-1,left/2,left.testBit 0,2*right⟩,true) := by
  unfold PhysicalNumeric.step
  rw [row]
  rfl

/-- On the stated full clean tape, the grammar path is silent and the next
literal transition is marked. Its exact post-event full tape is specified. -/
theorem root_beep_physical (code : List Bool) (hwalk : walk rootIndex code = some .beep)
    (head : Int) (leftTail rightTail : Nat) (physical : Machines.Config 285)
    (hrel : Rel (markedRootEntry code head leftTail rightTail) physical) :
    let left := bits (code.reverse++rootLeft) leftTail
    let sys := EventSystem.mk physical Record285.machine.step
    (∀ t, t < code.length → ¬ sys.BeepAt t) ∧
    sys.BeepAt code.length ∧
    Rel ⟨⟨1,by decide⟩,head-1,left/2,left.testBit 0,2*rightTail⟩
      (sys.run (code.length+1)) := by
  dsimp only
  let target : PhysicalNumeric.Config 285 :=
    ⟨beepState,head,bits (code.reverse++rootLeft) leftTail,true,rightTail⟩
  have hsymbolic := root_beep_symbolic code hwalk
  have hn := run_sound code.length
    (rightWord treeRoot (-(code.length:Int)) code true rootLeft [])
    ⟨beepState,0,code.reverse++rootLeft,true,[]⟩ hsymbolic head leftTail rightTail
  have hn' : silent Record285.machine code.length (markedRootEntry code head leftTail rightTail) =
      some target := by
    simpa only [markedRootEntry,target,denote,Int.add_zero,bits] using hn
  let sys := EventSystem.mk physical Record285.machine.step
  have hs := silent_physical Record285.machine (markedRootEntry code head leftTail rightTail)
    physical hrel code.length target hn'
  have hstep := step_related Record285.machine target (sys.run code.length) hs.1
  have hnstep := numeric_marked_left_step Record285.machine beepState ⟨1,by decide⟩ beep_row
    head (bits (code.reverse++rootLeft) leftTail) rightTail
  refine ⟨hs.2,?_,?_⟩
  · change (Record285.machine.step (sys.run code.length)).2 = true
    rw [← hstep.2,hnstep]
  · rw [EventSystem.run_succ]
    rw [hnstep] at hstep
    exact hstep.1


end Shared.PNP.Record285.Grammar
