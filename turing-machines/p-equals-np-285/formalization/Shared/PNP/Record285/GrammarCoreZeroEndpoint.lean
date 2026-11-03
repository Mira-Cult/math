import Shared.PNP.Record285.GrammarCoreZeroCertificate
import Shared.PNP.Record285.GrammarCoreZeroInvariant

/-! The five selected input-graph occurrences are zero on every reachable run.
Identification with the producer packet and the rewrite to the later graph
remain separate obligations. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.GrammarCoreZero
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarCoreGraph

theorem input_run_valid (n : Nat) : Valid inputRows masks ((coreSystem inputRows).run n) :=
  run_valid inputRows masks input_invariant_checked (by decide) n

/-- If any one of the five occurrence-specific tests is reached, its
selected register is zero in the actual full list bank. -/
theorem selected_tests_zero (n : Nat)
    (hselected : ((coreSystem inputRows).run n).index ∈ zeroRows) :
    ∃ reg no yes, reg < 15 ∧ inputRows[((coreSystem inputRows).run n).index]? = some ⟨.dec reg,no,yes⟩ ∧
      (((coreSystem inputRows).run n).fields.drop reg).headD 0 = 0 := by
  have hs := List.all_eq_true.mp selected_zero_checked _ hselected
  exact selectedZero_sound inputRows masks _ (input_run_valid n) hs

end Shared.PNP.Record285.GrammarCoreZero
