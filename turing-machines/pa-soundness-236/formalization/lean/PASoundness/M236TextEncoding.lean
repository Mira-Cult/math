import PASoundness.M236Data

/-!
Exact bit-events-v1 serialization used to bind the retained artifact text to
the Lean tables. The event label is the label on the taken row; the machine's
scalar beep field is not serialized by this format.
-/
namespace PASoundness.M236.TextEncoding

open Shared.Beeping Shared.Beeping.Machines

def digit (b : Bool) : String := if b then "1" else "0"

def eventText : Option Bool → String
  | none => "-"
  | some b => digit b

def moveText : Move → String
  | .left => "L"
  | .right => "R"

/-- Every field of a marked transition is rendered, including the input bit. -/
def rowText {n : Nat} (m : Machine n) (labels : BitLabels n)
    (q : Fin n) (read : Bool) : String :=
  let row := m.table.row q read
  toString q.val ++ " " ++ digit read ++ " " ++ digit row.write ++ " " ++
    moveText row.move ++ " " ++ toString row.next.val ++ " " ++
    eventText (labels.at q read) ++ "\n"

def headerText {n : Nat} (m : Machine n) : String :=
  "#! format bit-events-v1\n#! states " ++ toString n ++
  "\n#! start " ++ toString m.start.val ++ "\n#! blank " ++ digit m.blank ++
  "\n#! head " ++ toString m.startHead ++ "\n"

def bytes (s : String) : List UInt8 := s.toByteArray.data.toList

def rows {n : Nat} (m : Machine n) (labels : BitLabels n) : List (List UInt8) :=
  (List.ofFn fun q : Fin n =>
    [bytes (rowText m labels q false), bytes (rowText m labels q true)]).flatten

/-- The complete file's bytes, with each binary row and final newline. -/
def tableBytes {n : Nat} (m : Machine n) (labels : BitLabels n) : List UInt8 :=
  bytes (headerText m) ++ (rows m labels).flatten

example : rowText machine machineLabels 134 false = "134 0 1 L 71 1\n" := by decide
example : rowText machine machineLabels 137 true = "137 1 0 L 67 0\n" := by decide
example : rowText machine machineLabels 137 true ≠ "137 1 0 L 67 -\n" := by decide

end PASoundness.M236.TextEncoding
