import Shared.PNP.Record285.HalfDispatch

/-! Full-tape selection of an operand for the native-half operation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HalfSelector
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.IncrementSelector (blocksBits cost)
open Shared.PNP.Record285.DecrementSelector (Rows leftAfter)

def state : Nat → Fin 285
  | 0 => ⟨9,by decide⟩
  | d+1 => ⟨(70+d)%285,Nat.mod_lt _ (by decide)⟩

def rowCheck (d : Nat) : Bool :=
  decide (NumericTables.target.table.row (state (d+1)) false = ⟨false,.right,state d,false⟩) &&
  decide (NumericTables.target.table.row (state (d+1)) true = ⟨true,.right,state (d+1),false⟩)

theorem rows_checked : (List.range 5).all rowCheck = true := by decide

theorem literal_rows : Rows Record285.machine state 5 := by
  constructor <;> intro d hd
  · have h := List.all_eq_true.mp rows_checked d (List.mem_range.mpr hd)
    simp only [rowCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    simpa only [ArtifactEndpoint.literal_rows] using h.1
  · have h := List.all_eq_true.mp rows_checked d (List.mem_range.mpr hd)
    simp only [rowCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    simpa only [ArtifactEndpoint.literal_rows] using h.2

theorem literal_select (blocks : List Nat) (hbound : blocks.length+1 ≤ 5)
    (head : Int) (left tail : Nat) :
    silent Record285.machine (cost blocks)
      ⟨state (blocks.length+1),head,left,false,blocksBits blocks tail⟩ =
      some ⟨state 0,head+cost blocks,leftAfter blocks left,tail.testBit 0,tail/2⟩ :=
  DecrementSelector.select Record285.machine state 5 literal_rows blocks hbound head left tail

end Shared.PNP.Record285.HalfSelector
