import Shared.PNP.Record285.InitializationEdgeStart
import Shared.PNP.Record285.InitializationEdgeEnd
import Shared.PNP.Record285.InitializationRoundCheck0
import Shared.PNP.Record285.InitializationRoundCheck1
import Shared.PNP.Record285.InitializationRoundCheck2
import Shared.PNP.Record285.InitializationRoundCheck3
import Shared.PNP.Record285.InitializationShardComposition
import Shared.PNP.Record285.InitializationEntryLayout

/-! Exact physical blank-start initialization. This is a finite machine theorem;
it does not prove later progress or the source/complexity equivalence. -/
namespace Shared.PNP.Record285.InitializationComplete
open Shared.PNP.Record285.InitializationComposition
open Shared.PNP.Record285.InitializationShardComposition
open Shared.PNP.Record285.InitializationEntryLayout

theorem checked_cycles : ∀ n, 2 ≤ n → n < 1906 → InitializationRounds.checkRound n = true :=
  ranges_cover InitializationRoundCheck0.checked InitializationRoundCheck1.checked
    InitializationRoundCheck2.checked InitializationRoundCheck3.checked

/-- Exact complete numeric tape, absolute head and state at the finite
candidate source-entry boundary, with no earlier marked transitions. -/
theorem blank_start_entry :
    PhysicalNumeric.Rel candidate (Record285.machine.system.run 89806142) ∧
      ∀ t, t < 89806142 → ¬ Record285.machine.system.BeepAt t :=
  source_entry_of_certificates InitializationEdgeStart.edge checked_cycles InitializationEdgeEnd.edge

theorem blank_start_control :
    (Record285.machine.system.run 89806142).state.val = 284 ∧
      (Record285.machine.system.run 89806142).head = -3818 :=
  candidate_control _ blank_start_entry.1

/-- The same result with a cellwise characterization of the complete tape. -/
theorem blank_start_tape (pos : Int) :
    (Record285.machine.system.run 89806142).tape pos = true ↔
      pos = -3821 ∨ pos = -3820 ∨ (3 ≤ pos ∧ pos ≤ 3821 ∧ pos % 2 = 1) :=
  candidate_tape _ blank_start_entry.1 pos

/-- The candidate entry tape begins with `110`, followed by the complete
blank gap to the bank anchor. -/
theorem blank_start_root_and_gap :
    (Record285.machine.system.run 89806142).tape (-3821) = true ∧
    (Record285.machine.system.run 89806142).tape (-3820) = true ∧
      ∀ x, -3819 ≤ x → x ≤ 2 → (Record285.machine.system.run 89806142).tape x = false :=
  candidate_root_and_gap _ blank_start_entry.1

/-- The anchor and all 1,909 consecutive zero blocks have the stated
one-zero encoding. Their source-level allocation is a separate obligation. -/
theorem blank_start_zero_bank :
    (Record285.machine.system.run 89806142).tape 3 = true ∧
    (Record285.machine.system.run 89806142).tape 4 = false ∧
      ∀ i : Nat, i < 1909 →
        (Record285.machine.system.run 89806142).tape (5+2*(i:Int)) = true ∧
        (Record285.machine.system.run 89806142).tape (6+2*(i:Int)) = false :=
  candidate_zero_bank _ blank_start_entry.1

end Shared.PNP.Record285.InitializationComplete
