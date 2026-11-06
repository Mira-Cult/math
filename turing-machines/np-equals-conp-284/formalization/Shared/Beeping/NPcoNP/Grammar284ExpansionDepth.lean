import Shared.Beeping.NPcoNP.Grammar284Depth
import Shared.Beeping.NPcoNP.ExpansionTrace.Final
/-! Concrete path bounds for all nodes and leaves of the certified
expansion used by the producer graph. -/
namespace Shared.Beeping.NPcoNP.Grammar284ExpansionDepth

open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

def pathCheck (p : Path) : Bool := decide (p.length≤55) && decide (p.count false≤11)

theorem checked_leaves : traceState557.acc.leaves.toList.all (fun x => pathCheck x.1) = true := by decide
theorem checked_starts : traceState557.acc.starts.toList.all (fun x => pathCheck x.1) = true := by decide


theorem expanded_leaf_bounds (e : Expansion)
    (he : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some e)
    (entry : Path × String) (hmem : entry ∈ e.leaves.toList) :
    entry.1.length≤55 ∧ entry.1.count false≤11 := by
  rw [producerExpand] at he
  cases he
  have hc := List.all_eq_true.mp checked_leaves entry hmem
  simpa [pathCheck] using hc

theorem expanded_start_bounds (e : Expansion)
    (he : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some e)
    (entry : Path × Nat) (hmem : entry ∈ e.starts.toList) :
    entry.1.length≤55 ∧ entry.1.count false≤11 := by
  rw [producerExpand] at he
  cases he
  have hc := List.all_eq_true.mp checked_starts entry hmem
  simpa [pathCheck] using hc

theorem checked_height_witness :
    traceState557.acc.leaves.toList.any (fun x => decide (x.1.length=55)) = true := by decide

theorem checked_zero_witness :
    traceState557.acc.leaves.toList.any (fun x => decide (x.1.count false=11)) = true := by decide

theorem expanded_height_attained (e : Expansion)
    (he : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some e) :
    ∃ entry ∈ e.leaves.toList, entry.1.length=55 := by
  rw [producerExpand] at he
  cases he
  obtain ⟨entry, hm, hh⟩ := List.any_eq_true.mp checked_height_witness
  exact ⟨entry,hm,of_decide_eq_true hh⟩

theorem expanded_zero_attained (e : Expansion)
    (he : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some e) :
    ∃ entry ∈ e.leaves.toList, entry.1.count false=11 := by
  rw [producerExpand] at he
  cases he
  obtain ⟨entry, hm, hh⟩ := List.any_eq_true.mp checked_zero_witness
  exact ⟨entry,hm,of_decide_eq_true hh⟩

#print axioms expanded_leaf_bounds
#print axioms expanded_height_attained
#print axioms expanded_zero_attained

/-- The full-graph definition uses exactly the seed checked above. -/
theorem fullGraph_expansion_seed (g : Grammar) (fuel : Nat) :
    fullGraph g fuel = (do
      let e ← expand g.nodes fuel (.node g.root) preparedPrefix [] {}
      (← e.leaves.toList.mapM (fullRow e.starts)).toArray) := by
  rfl

#print axioms fullGraph_expansion_seed
end Shared.Beeping.NPcoNP.Grammar284ExpansionDepth
