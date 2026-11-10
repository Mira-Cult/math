import PASoundness.M236OccurrenceGraphDeterminism
namespace PASoundness.M236.OccurrenceGraph
example : nextIndex "3.k.stage.decnz" 1 (some 4) (fun _ => 0) = 4 := by decide
example : nextIndex "3.k.stage.decnz" 1 (some 4) (fun _ => 1000000) = 1 := by decide
example : nextReserve "3.k.stage.decnz" (fun _ => 1000000) [7] = [7, 0] := by decide
example : nextReserve "3.k.stage.decnz" (fun _ => 0) [7] = [7] := by decide
example : (nextBank "3.k.a.inc" (fun _ => 1000000)) 6 = 1000001 := by decide
example : (nextBank "3.k.a.decnz" (fun _ => 1000000)) 6 = 999999 := by decide
example : outputForOp "emit.0" ≠ outputForOp "emit.1" := by decide
end PASoundness.M236.OccurrenceGraph
