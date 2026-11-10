import PASoundness.M236MetadataNames
import PASoundness.M236TextEncoding

/-! Canonical JSON rows for the finite grammar, node names and physical state
names. Exact file binding is established separately from these definitions. -/
namespace PASoundness.M236.Metadata
open PASoundness.M236.Grammar PASoundness.M236.TextEncoding

def separator : List UInt8 := [44, 10]

def quote (s : String) : String := "\"" ++ s ++ "\""

def childText : Edge → String
  | .node i => toString i.val
  | .leaf name .. => quote name

def grammarItem (i : Fin 158) : String :=
  "    " ++ quote (toString i.val) ++ ": [\n      " ++ childText nodes[i].zero ++
  ",\n      " ++ childText nodes[i].one ++ "\n    ]"

def nameItem (i : Fin 158) : String :=
  "    " ++ quote (toString i.val) ++ ": " ++ quote stateNames[nodes[i].state]

def stateItem (q : Fin 237) : String :=
  "    " ++ quote stateNames[q] ++ ": " ++ toString q.val

def grammarRows : List (List UInt8) := grammarOrder.map (bytes ∘ grammarItem)
def nameRows : List (List UInt8) := grammarOrder.map (bytes ∘ nameItem)
def stateRows : List (List UInt8) := stateOrder.map (bytes ∘ stateItem)

def rootText : String := "  \"grammar_root\": " ++ toString (157 : Nat) ++ ",\n"
def dispatchText : String :=
  "  \"run_dispatch\": {\n    \"leaf_paths\": 760,\n    \"max_zero_run\": 5,\n    \"prefix\": \"110\",\n    \"threshold\": 6\n  },\n"

end PASoundness.M236.Metadata
