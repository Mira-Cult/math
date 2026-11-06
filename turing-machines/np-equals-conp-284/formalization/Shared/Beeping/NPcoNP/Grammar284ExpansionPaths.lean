import Shared.Beeping.NPcoNP.Grammar284ExpansionDepth
/-! Replay every certified expansion path through the parsed grammar.
This does not identify grammar paths with physical tape configurations. -/
namespace Shared.Beeping.NPcoNP.Grammar284ExpansionPaths

open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option maxRecDepth 131072
set_option maxHeartbeats 40000000

def leafPathOK (e : Path × String) : Bool :=
  (e.1.take 3 == preparedPrefix) &&
    (follow producerGrammar (.node producerGrammar.root) (e.1.drop 3) == some (.op e.2))

theorem allLeafPaths : traceState557.acc.leaves.toList.all leafPathOK = true := by decide

#print axioms allLeafPaths

theorem expanded_leaf_follows (e : Expansion)
    (he : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some e)
    (entry : Path × String) (hmem : entry ∈ e.leaves.toList) :
    PreparedWalk entry.1 (.op entry.2) := by
  rw [producerExpand] at he
  cases he
  have hc := List.all_eq_true.mp allLeafPaths entry hmem
  simp only [leafPathOK, Bool.and_eq_true, beq_iff_eq] at hc
  have hpre := hc.1
  have hrun := hc.2
  refine ⟨entry.1.drop 3, ?_, follow_sound producerGrammar _ _ _ hrun⟩
  calc
    entry.1 = entry.1.take 3 ++ entry.1.drop 3 := (List.take_append_drop 3 entry.1).symm
    _ = preparedPrefix ++ entry.1.drop 3 := by rw [hpre]

#print axioms expanded_leaf_follows

def startPathOK (e : Path × Nat) : Bool :=
  (e.1.take 3 == preparedPrefix) &&
    (follow producerGrammar (.node producerGrammar.root) (e.1.drop 3)).isSome

theorem allStartPaths : traceState557.acc.starts.toList.all startPathOK = true := by decide

theorem expanded_start_follows (e : Expansion)
    (he : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some e)
    (entry : Path × Nat) (hmem : entry ∈ e.starts.toList) :
    ∃ last, PreparedWalk entry.1 last := by
  rw [producerExpand] at he
  cases he
  have hc := List.all_eq_true.mp allStartPaths entry hmem
  simp only [startPathOK, Bool.and_eq_true, beq_iff_eq] at hc
  cases hr : follow producerGrammar (.node producerGrammar.root) (entry.1.drop 3) with
  | none => simp [hr] at hc
  | some last =>
    refine ⟨last,entry.1.drop 3,?_,follow_sound producerGrammar _ _ _ hr⟩
    calc
      entry.1 = entry.1.take 3 ++ entry.1.drop 3 := (List.take_append_drop 3 entry.1).symm
      _ = preparedPrefix ++ entry.1.drop 3 := by rw [hc.1]

#print axioms expanded_start_follows

/-- The grammar-level proof also bounds each recorded expansion leaf. -/
theorem expanded_leaf_semantic_bounds (e : Expansion)
    (he : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some e)
    (entry : Path × String) (hmem : entry ∈ e.leaves.toList) :
    entry.1.length≤55 ∧ entry.1.count false≤11 :=
  prepared_path_bound entry.1 (.op entry.2) (expanded_leaf_follows e he entry hmem)

/-- Every recorded expansion start can finish at a leaf while respecting
both prepared-path bounds. -/
theorem expanded_start_can_finish (e : Expansion)
    (he : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some e)
    (entry : Path × Nat) (hmem : entry ∈ e.starts.toList) :
    ∃ last suffix name, PreparedWalk entry.1 last ∧
      Walk producerGrammar last suffix (.op name) ∧
      entry.1.length+suffix.length≤55 ∧
      entry.1.count false+suffix.count false≤11 := by
  obtain ⟨last,raw,heq,hwalk⟩ := expanded_start_follows e he entry hmem
  obtain ⟨suffix,name,hfinish,hl,hz⟩ := producer_prefix_finishes raw last hwalk
  refine ⟨last,suffix,name,⟨raw,heq,hwalk⟩,hfinish,?_,?_⟩
  · rw [heq]
    simp [preparedPrefix] at ⊢
    omega
  · rw [heq]
    simp [preparedPrefix,List.count_append] at ⊢
    omega

#print axioms expanded_leaf_semantic_bounds
#print axioms expanded_start_can_finish

end Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
