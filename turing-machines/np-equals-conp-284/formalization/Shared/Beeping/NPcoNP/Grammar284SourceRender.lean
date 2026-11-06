import Shared.Beeping.NPcoNP.Grammar284Data

/-! A total character-list renderer for the selected fixed-indentation
grammar layout. It emits literal, unescaped operation and register names;
the existing safe-string predicates are needed when interpreting those names
as JSON strings. This module does not prove a relation to the source bytes. -/

namespace Shared.Beeping.NPcoNP.Grammar284.SourceRender

/-- Join fields with the exact comma/newline delimiter. -/
def join (xs : List (List Char)) : List Char :=
  (xs.intersperse ",\n".toList).flatten

/-- Render one leaf object at the indentation used for grammar nodes. -/
def leaf : Leaf → List Char
  | .op s => "      {\n        \"op\": \"".toList ++ s.toList ++ "\"\n      }".toList
  | .node n => "      {\n        \"node\": ".toList ++ (toString n).toList ++ "\n      }".toList

/-- Render one two-leaf node, without its following delimiter. -/
def node (p : Leaf × Leaf) : List Char :=
  "    [\n".toList ++ leaf p.1 ++ ",\n".toList ++ leaf p.2 ++ "\n    ]".toList

/-- Render node entries with an arbitrary remaining suffix. The final entry
ends in a newline; intermediate entries end in comma/newline. -/
def nodes (xs : List (Leaf × Leaf)) (tail : List Char) : List Char :=
  match xs with
  | [] => tail
  | [p] => node p ++ "\n".toList ++ tail
  | p :: q :: rest => node p ++ ",\n".toList ++ nodes (q :: rest) tail

def register (s : String) : List Char := "    \"".toList ++ s.toList ++ "\"".toList

/-- Everything after the node entries, including the final newline. -/
def footer (g : Grammar) : List Char :=
  "  ],\n  \"registers\": [\n".toList ++ join (g.registers.toList.map register) ++
    "\n  ],\n  \"root\": ".toList ++ (toString g.root).toList ++ "\n}\n".toList

def render (g : Grammar) : List Char :=
  "{\n  \"nodes\": [\n".toList ++ nodes g.nodes.toList (footer g)

end Shared.Beeping.NPcoNP.Grammar284.SourceRender
