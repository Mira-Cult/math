import Shared.PNP.Record285.GrammarReady
import Shared.PNP.Record285.CleanBankFirstStep

/-! The actual blank-start control and bank satisfy the generic anchored
valid-prefix invariant. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarReady
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarPrefix
open Shared.PNP.Record285.CleanBank

theorem initial_anchored_root :
    AnchoredRoot (List.replicate 1909 0) (-3818) 3
      (Record285.machine.system.run 89806142) := by
  have hprefix : valid [false] := ⟨.inc 6,walk_follow [false] rootIndex (.inc 6) initial_increment_path⟩
  refine ⟨[],false,-3818,0,3819,?_,by decide,by decide,?_⟩
  · simpa using hprefix
  · change Rel (denote (rightWord treeRoot 0 [] false rootLeft [false]) (-3818) 0
      (runPattern false 3819 true (2*IncrementSelector.blocksBits (List.replicate 1909 0) 0))) _
    rw [← candidate_clean_numeric]
    exact InitializationComplete.blank_start_entry.1

/-- The generic, unbounded-field admission theorem applies at the actual
blank-start boundary. -/
theorem initial_grammar_ready :
    ∃ e, Ready e (List.replicate 1909 0) (Record285.machine.system.run 89806142) := by
  apply ready_of_good_root
  · simp
  · exact anchored_is_good _ (-3818) 3 _ initial_anchored_root (by decide)

end Shared.PNP.Record285.GrammarReady
