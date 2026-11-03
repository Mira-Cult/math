import Shared.PNP.Record285.DecrementNonzeroComposition

/-! Leftward suffix shift for the positive decrement case. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementNonzeroShift
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementShift (atWord even_bit even_tail)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeBits completeCost)
open Shared.PNP.Record285.IncrementMeaning (foldRuns)

def check : Fin 285 := ⟨49,by decide⟩
def returnState : Fin 285 := ⟨51,by decide⟩

structure Rows (M : Machine 285) (scan check ret : Fin 285) : Prop where
  scanOne : M.table.row scan true = ⟨true,.left,scan,false⟩
  scanZero : M.table.row scan false = ⟨true,.left,check,false⟩
  checkOne : M.table.row check true = ⟨false,.left,scan,false⟩
  checkZero : M.table.row check false = ⟨false,.left,ret,false⟩

def shiftedRight : List Nat → Nat → Nat → Nat
  | [],last,right => 4*pushBit last true right+2
  | k::ks,last,right => shiftedRight ks last (4*pushBit k true right+2)

theorem shift_block (M : Machine 285) (scan check ret : Fin 285)
    (rows : Rows M scan check ret) (k : Nat) (head : Int) (word right : Nat) :
    silent M (k+2) (atLeftWord scan head (runPattern true k false (1+2*word)) right) =
      some (atLeftWord scan (head-(k+2)) word (4*pushBit k true right+2)) := by
  have hs := IncrementCleanup.sweep_left M scan true true rows.scanOne k false head (1+2*word) right
  have hp : silent M 2
      (atLeftWord scan (head-k) (2*(1+2*word)) (pushBit k true right)) =
      some (atLeftWord scan (head-k-2) word (4*pushBit k true right+2)) := by
    simp only [atLeftWord,even_bit,even_tail,odd_bit,odd_tail,silent,PhysicalNumeric.step,
      rows.scanZero,rows.checkOne,Bool.false_eq_true,if_false,bitVal,if_true,Nat.add_zero]
    have hh : head-(k:Int)-1-1 = head-(k:Int)-2 := by omega
    have hr : 2*(2*pushBit k true right+1) = 4*pushBit k true right+2 := by omega
    simp only [hh,hr]
  rw [silent_add,hs]
  simp only [Option.bind_some,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  have hh : head-(k:Int)-2 = head-((k+2:Nat):Int) := by omega
  simpa only [Int.natCast_add,show ((2:Nat):Int)=2 by rfl,hh] using hp

theorem shift_final (M : Machine 285) (scan check ret : Fin 285)
    (rows : Rows M scan check ret) (k : Nat) (head : Int) (far right : Nat) :
    silent M (k+2) (atLeftWord scan head (runPattern true k false (2*far)) right) =
      some (atLeftWord ret (head-(k+2)) far (4*pushBit k true right+2)) := by
  have hs := IncrementCleanup.sweep_left M scan true true rows.scanOne k false head (2*far) right
  have hp : silent M 2 (atLeftWord scan (head-k) (2*(2*far)) (pushBit k true right)) =
      some (atLeftWord ret (head-k-2) far (4*pushBit k true right+2)) := by
    simp only [atLeftWord,even_bit,even_tail,silent,PhysicalNumeric.step,
      rows.scanZero,rows.checkZero,Bool.false_eq_true,if_false,bitVal,if_true,Nat.add_zero]
    have hh : head-(k:Int)-1-1 = head-(k:Int)-2 := by omega
    have hr : 2*(2*pushBit k true right+1) = 4*pushBit k true right+2 := by omega
    simp only [hh,hr]
  rw [silent_add,hs]
  simp only [Option.bind_some,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  have hh : head-(k:Int)-2 = head-((k+2:Nat):Int) := by omega
  simpa only [Int.natCast_add,show ((2:Nat):Int)=2 by rfl,hh] using hp

/-- Shift a whole finite reverse bank to the left, preserving the uninspected
far prefix and producing an explicit complete right tape. -/
theorem shift_complete (M : Machine 285) (scan check ret : Fin 285)
    (rows : Rows M scan check ret) (runs : List Nat) (last : Nat)
    (head : Int) (far right : Nat) :
    silent M (completeCost runs last) (atLeftWord scan head (completeBits runs last far) right) =
      some (atLeftWord ret (head-completeCost runs last) far (shiftedRight runs last right)) := by
  induction runs generalizing head right with
  | nil => exact shift_final M scan check ret rows last head far right
  | cons k ks ih =>
    have hb := shift_block M scan check ret rows k head (completeBits ks last far) right
    have hr := ih (head-(k+2)) (4*pushBit k true right+2)
    simp only [completeBits,completeCost,shiftedRight]
    rw [silent_add,hb]
    simp only [Option.bind_some]
    have hh : head-((k:Int)+2)-(completeCost ks last:Int) =
        head-((k:Int)+2+(completeCost ks last:Int)) := by omega
    simpa only [Int.natCast_add,show ((2:Nat):Int)=2 by rfl,hh] using hr

theorem literal_rows : Rows Record285.machine DecrementNonzeroScan.shift check returnState := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

end Shared.PNP.Record285.DecrementNonzeroShift
