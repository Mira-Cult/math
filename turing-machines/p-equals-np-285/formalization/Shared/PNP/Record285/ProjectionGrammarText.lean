import Shared.PNP.Record285.ProducerGrammar

/-! Exact JSON rendering of the 21-register producer grammar. -/
namespace Shared.PNP.Record285.ProducerGrammar
open Shared.PNP.Record285.Grammar

def literal : String := include_str "producer-pre-projection.json"

def edgeField (names : Array String) : Edge → String
  | .node n => "\"node\": " ++ toString n
  | .inc n => "\"op\": \"3." ++ names[n]?.getD "INVALID" ++ ".inc\""
  | .dec n => "\"op\": \"3." ++ names[n]?.getD "INVALID" ++ ".decnz\""
  | .half n => "\"op\": \"3.$native-half:" ++ names[n]?.getD "INVALID" ++ ".decnz\""
  | .beep => "\"op\": \"beep\""
  | .brk n => "\"op\": \"_break." ++ toString n ++ "\""
  | .cont n => "\"op\": \"_continue." ++ toString n ++ "\""

def renderEntry (names : Array String) (entry : Entry) : List Char :=
  let n := entry.1
  ("    [\n      {\n        " ++ edgeField names n.1 ++
    "\n      },\n      {\n        " ++ edgeField names n.2 ++
    "\n      }\n    ]" ++ (if entry.2 then "\n" else ",\n")).toList

def renderEntries (names : Array String) : List Entry → List Char
  | [] => []
  | e::es => renderEntry names e ++ renderEntries names es

theorem renderEntries_append (names : Array String) (xs ys : List Entry) :
    renderEntries names (xs++ys) = renderEntries names xs ++ renderEntries names ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [renderEntries,ih,List.append_assoc]

def renderNames : List String → String
  | [] => ""
  | [n] => "    \"" ++ n ++ "\"\n"
  | n::ns => "    \"" ++ n ++ "\",\n" ++ renderNames ns

def renderSuffix (g : Data) : List Char :=
  ("  ],\n  \"registers\": [\n" ++ renderNames g.names.toList ++
   "  ],\n  \"root\": " ++ toString g.root ++ "\n}\n").toList

end Shared.PNP.Record285.ProducerGrammar
