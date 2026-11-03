import Shared.PNP.Record285.DecrementNonzeroLayout

/-! Compose the nonzero suffix scan with its exact leftward shift. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementNonzeroShiftRun
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.BootstrapChecker (silent_compose)
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementShift (atWord even_bit even_tail)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeBits completeCost)
open Shared.PNP.Record285.IncrementMeaning (foldRuns)
open Shared.PNP.Record285.DecrementNonzeroShift (shiftedRight)
attribute [local irreducible] Record285.machine

theorem shift_entry (M : Machine 285) (scan check ret : Fin 285)
    (rows : DecrementNonzeroShift.Rows M scan check ret)
    (head : Int) (word retained : Nat) :
    silent M 2 (atWord scan head (1+2*word) (4*retained)) =
      some (atLeftWord scan (head-2) word (8*retained+2)) := by
  rw [show 4*retained = 2*(2*retained) by omega]
  simp only [atWord,atLeftWord,even_bit,even_tail,odd_bit,odd_tail,silent,
    PhysicalNumeric.step,rows.scanZero,rows.checkOne,Bool.false_eq_true,if_false,
    bitVal,if_true,Nat.add_zero]
  have hh : head-1-1 = head-2 := by omega
  have hr : 2*(2*(2*retained)+1) = 8*retained+2 := by omega
  simp only [hh,hr]

/-- From the end of the rightward scan, shift every suffix field left and
reach the ordinary return scanner, with an explicit reconstructed bank. -/
theorem shift_to_return (fields : List Nat) (k : Nat) (head : Int) (middle retained : Nat) :
    silent Record285.machine (2+completeCost (foldRuns fields []) k)
      (atWord DecrementNonzeroScan.shift head
        (DecrementNonzeroScan.scannedLeft k fields (4*(2*middle)+1)) (4*retained)) =
      some (atLeftWord DecrementNonzeroShift.returnState
        (head-2-completeCost (foldRuns fields []) k) middle
        (2*IncrementSelector.blocksBits (k::fields) (4*retained+1))) := by
  let runs := foldRuns fields []
  let word := completeBits runs k middle
  have hl := DecrementNonzeroLayout.scan_layout fields k middle
  have he := shift_entry Record285.machine DecrementNonzeroScan.shift
    DecrementNonzeroShift.check DecrementNonzeroShift.returnState
    DecrementNonzeroShift.literal_rows head word retained
  have hs := DecrementNonzeroShift.shift_complete Record285.machine DecrementNonzeroScan.shift
    DecrementNonzeroShift.check DecrementNonzeroShift.returnState
    DecrementNonzeroShift.literal_rows runs k (head-2) middle (8*retained+2)
  have ho := DecrementNonzeroLayout.shifted_output fields k retained
  rw [ho] at hs
  rw [hl,silent_add,he]
  simp only [Option.bind_some]
  exact hs

theorem shift_to_return_physical (fields : List Nat) (k : Nat)
    (head : Int) (middle retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (atWord DecrementNonzeroScan.shift head
      (DecrementNonzeroScan.scannedLeft k fields (4*(2*middle)+1)) (4*retained)) physical) :
    let steps := 2+completeCost (foldRuns fields []) k
    Rel (atLeftWord DecrementNonzeroShift.returnState
      (head-2-completeCost (foldRuns fields []) k) middle
      (2*IncrementSelector.blocksBits (k::fields) (4*retained+1)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (shift_to_return fields k head middle retained)
  exact ⟨hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.DecrementNonzeroShiftRun
