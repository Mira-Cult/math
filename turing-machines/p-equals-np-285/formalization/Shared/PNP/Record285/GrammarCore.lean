import Shared.PNP.Record285.DispatcherIncrement

/-! Finite producer control grammar, its exact JSON serialization, and a
row-level interface to the literal marked machine. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping.Machines
open Shared.PNP.Record285.GenericDispatch

inductive Edge where
  | node (index : Nat)
  | inc (index : Nat)
  | dec (index : Nat)
  | half (index : Nat)
  | beep
  | brk (index : Nat)
  | cont (index : Nat)
  deriving DecidableEq, Repr

abbrev Node := Edge × Edge
abbrev Entry := Node × Bool

def edgeField : Edge → String
  | .node n => "\"node\": " ++ toString n
  | .inc n => "\"op\": \"3.$coalesced." ++ toString n ++ ".inc\""
  | .dec n => "\"op\": \"3.$coalesced." ++ toString n ++ ".decnz\""
  | .half n => "\"op\": \"3.$native-half:$coalesced." ++ toString n ++ ".decnz\""
  | .beep => "\"op\": \"beep\""
  | .brk n => "\"op\": \"_break." ++ toString n ++ "\""
  | .cont n => "\"op\": \"_continue." ++ toString n ++ "\""

def renderEntry (entry : Entry) : List Char :=
  let n := entry.1
  ("    [\n      {\n        " ++ edgeField n.1 ++
    "\n      },\n      {\n        " ++ edgeField n.2 ++
    "\n      }\n    ]" ++ (if entry.2 then "\n" else ",\n")).toList

def renderEntries : List Entry → List Char
  | [] => []
  | e::es => renderEntry e ++ renderEntries es

theorem renderEntries_append (xs ys : List Entry) :
    renderEntries (xs++ys) = renderEntries xs ++ renderEntries ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [renderEntries,ih,List.append_assoc]

def literal : String := include_str "producer-grammar.json"

end Shared.PNP.Record285.Grammar
