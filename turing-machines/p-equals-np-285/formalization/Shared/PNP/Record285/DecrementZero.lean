import Shared.PNP.Record285.DecrementSelector
import Shared.PNP.Record285.IncrementReturn

/-! The ordinary decrement zero case through its complete return scanner. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementZero
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementShift (even_bit even_tail)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeBits completeCost completeRight)

def probe : Fin 285 := ⟨45,by decide⟩
def scan : Fin 285 := ⟨53,by decide⟩
def check : Fin 285 := ⟨54,by decide⟩
def breakOne : Fin 285 := ⟨117,by decide⟩

structure BranchRows (M : Machine 285) (target probeState scanState : Fin 285) : Prop where
  targetOne : M.table.row target true = ⟨false,.right,probeState,false⟩
  probeZero : M.table.row probeState false = ⟨false,.left,target,false⟩
  targetZero : M.table.row target false = ⟨true,.left,scanState,false⟩

theorem zero_entry (M : Machine 285) (target probeState scanState : Fin 285)
    (rows : BranchRows M target probeState scanState) (head : Int) (left suffix : Nat) :
    silent M 3 ⟨target,head,left,true,2*suffix⟩ =
      some (atLeftWord scanState (head-1) left (4*suffix+1)) := by
  simp only [silent,PhysicalNumeric.step,rows.targetOne,rows.probeZero,rows.targetZero,
    Bool.false_eq_true,if_false,bitVal,if_true,Nat.add_zero,even_bit,even_tail,atLeftWord]
  have hh : head+1-1-1 = head-1 := by omega
  have hr : 2*(2*suffix)+1 = 4*suffix+1 := by omega
  simp only [hh,hr]

theorem literal_branch_rows : BranchRows Record285.machine (DecrementSelector.state 0) probe scan := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

theorem literal_scan_rows : IncrementReturn.Rows Record285.machine scan check breakOne := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

/-- The selector's left word ends with a valid double-zero return layout.
Every preceding unary block and the full far-left word are retained. -/
theorem selector_left_layout (blocks runs : List Nat) (last farLeft : Nat) :
    ∃ runs' last', DecrementSelector.leftAfter blocks (1+2*completeBits runs last farLeft) =
      2*(1+2*completeBits runs' last' farLeft) := by
  induction blocks generalizing runs last with
  | nil => exact ⟨runs,last,rfl⟩
  | cons k ks ih =>
    simp only [DecrementSelector.leftAfter,IncrementReturn.push_field_layout]
    exact ih (k::runs) last

theorem return_layout (gap : Nat) (before : List Nat) (farLeft : Nat) :
    ∃ runs last, DecrementSelector.leftAfter (gap::before) (2*farLeft) =
      completeBits (0::runs) last farLeft := by
  have hfirst : pushBit (gap+1) true (2*(2*farLeft)) =
      1+2*completeBits [] gap farLeft := by
    rw [IncrementReturn.push_run]
    simp only [runPattern,completeBits,bitVal,if_true]
  obtain ⟨runs,last,hleft⟩ := selector_left_layout before [] gap farLeft
  refine ⟨runs,last,?_⟩
  change DecrementSelector.leftAfter before (pushBit (gap+1) true (2*(2*farLeft))) = _
  rw [hfirst,hleft]
  simp only [completeBits,runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]

/-- A zero unary field returns to the one-level break state in finite silent
time; the returned right tape is the scanner's exact full word. -/
theorem zero_to_break (gap : Nat) (before : List Nat) (head : Int) (farLeft suffix : Nat) :
    ∃ runs last,
      silent Record285.machine (3+completeCost (0::runs) last)
        ⟨DecrementSelector.state 0,head,
          DecrementSelector.leftAfter (gap::before) (2*farLeft),true,2*suffix⟩ =
        some (atLeftWord breakOne (head-1-completeCost (0::runs) last) farLeft
          (completeRight (0::runs) last (4*suffix+1))) := by
  obtain ⟨runs,last,hlayout⟩ := return_layout gap before farLeft
  refine ⟨runs,last,?_⟩
  have hz := zero_entry Record285.machine (DecrementSelector.state 0) probe scan
    literal_branch_rows head (DecrementSelector.leftAfter (gap::before) (2*farLeft)) suffix
  have hs := IncrementReturn.scan_complete Record285.machine scan check breakOne literal_scan_rows
    (0::runs) last (head-1) farLeft (4*suffix+1)
  rw [hlayout] at hz
  rw [hlayout,silent_add,hz]
  simp only [Option.bind_some]
  exact hs

theorem zero_to_break_physical (gap : Nat) (before : List Nat) (head : Int)
    (farLeft suffix : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨DecrementSelector.state 0,head,
      DecrementSelector.leftAfter (gap::before) (2*farLeft),true,2*suffix⟩ physical) :
    ∃ runs last,
      Rel (atLeftWord breakOne (head-1-completeCost (0::runs) last) farLeft
        (completeRight (0::runs) last (4*suffix+1)))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run
          (3+completeCost (0::runs) last)) ∧
      (∀ t, t < 3+completeCost (0::runs) last →
        ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
      0 < 3+completeCost (0::runs) last := by
  obtain ⟨runs,last,h⟩ := zero_to_break gap before head farLeft suffix
  have hp := silent_physical Record285.machine _ physical hrel _ _ h
  exact ⟨runs,last,hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.DecrementZero
