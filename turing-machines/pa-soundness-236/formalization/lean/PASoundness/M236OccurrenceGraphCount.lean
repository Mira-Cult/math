import PASoundness.M236OccurrenceGraphData
/-! Cardinality of the retained finite occurrence witness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph

def edgeCount : Nat := sourceRows.toList.foldl
  (fun count (_, _, extra) => count + if extra.isSome then 2 else 1) 0

theorem edge_count : edgeCount = 1036 := by decide
end PASoundness.M236.OccurrenceGraph
