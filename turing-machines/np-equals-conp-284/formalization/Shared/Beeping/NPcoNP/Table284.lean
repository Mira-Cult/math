import Shared.Beeping.NPcoNP.Table284Data
import Shared.Beeping.TableSyntax

/-! The generated numeric data define a finite binary machine. This module
proves the parser round trip for those data; it does not yet connect them to
all bytes of the original ASCII table or to the producer's infinite run. -/
namespace Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.Machines Shared.Beeping.TableBits

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem rows_length : data.2.length = 284 := by decide

theorem rows_valid : validRows 284 data.2 = true := by decide

def machine : Machine 284 := assemble data ⟨0, by decide⟩

theorem machine_data : TableBits.data machine = data := by
  apply Shared.Beeping.TableSyntax.data_assemble_of_valid
  · rfl
  · exact rows_length
  · exact rows_valid

theorem parse_generated_data : parseData 284 data = some machine := by
  unfold parseData
  simp only [show data.1.1 < 284 from by decide, dite_true]
  change (if TableBits.data machine = data then some machine else none) = some machine
  rw [machine_data]
  simp

theorem machine_starts_zero : machine.start.val = 0 ∧ machine.blank = false ∧
    machine.startHead = 0 := by decide

end Shared.Beeping.NPcoNP.Table284
