import PASoundness.M236OccurrenceGraphData
/-! File-specific serializer for the retained occurrence graph. -/
namespace PASoundness.M236.OccurrenceGraph.Text
open PASoundness.M236.OccurrenceGraph

def rowText (row : String × Nat × Option Nat) : String :=
  let (name, dest, extra) := row
  "[\"" ++ name ++ "\"," ++ toString dest ++
    (match extra with | none => "" | some target => "," ++ toString target) ++ "]"

def groupText (rows : Array (String × Nat × Option Nat)) (i : Nat) : String :=
  String.intercalate "," (((rows.toList.drop (95 * i)).take 95).map rowText)

def serialize (rows : Array (String × Nat × Option Nat)) : String :=
  "[" ++ groupText rows 0 ++ "," ++ groupText rows 1 ++ "," ++ groupText rows 2 ++ "," ++ groupText rows 3 ++ "," ++ groupText rows 4 ++ "," ++ groupText rows 5 ++ "," ++ groupText rows 6 ++ "," ++ groupText rows 7 ++ "]\n"
end PASoundness.M236.OccurrenceGraph.Text
