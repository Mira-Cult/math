import Shared.PNP.Record285.GrammarCoreGraphData

/-! Exact serialization format of the producer's extracted core-graph field. -/
namespace Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.Grammar

def sourceFragment : String := include_str "producer-core-fragment.txt"

def renderOperation : Edge → String
  | .inc i => "3.$coalesced." ++ toString i ++ ".inc"
  | .dec i => "3.$coalesced." ++ toString i ++ ".decnz"
  | .half i => "3.$native-half:$coalesced." ++ toString i ++ ".decnz"
  | .beep => "beep"
  | _ => "INVALID"

def renderEntry (entry : CoreRow × Bool) : List Char :=
  let row := entry.1
  let binary := match row.edge with | .dec _ | .half _ => true | _ => false
  ("      [\n        \"" ++ renderOperation row.edge ++ "\",\n        " ++
    toString row.no ++ (if binary then ",\n        " ++ toString row.yes else "") ++
    "\n      ]" ++ (if entry.2 then "\n" else ",\n")).toList

def renderEntries : List (CoreRow × Bool) → List Char
  | [] => []
  | entry::rest => renderEntry entry ++ renderEntries rest

theorem renderEntries_append (xs ys : List (CoreRow × Bool)) :
    renderEntries (xs++ys) = renderEntries xs ++ renderEntries ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [renderEntries,ih,List.append_assoc]

end Shared.PNP.Record285.GrammarCoreGraph
