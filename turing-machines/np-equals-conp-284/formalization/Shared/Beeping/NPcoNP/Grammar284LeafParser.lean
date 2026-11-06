import Shared.Beeping.NPcoNP.Grammar284NodeLeaf
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Concrete parser for the selected node/op leaf layout. -/
namespace Shared.Beeping.NPcoNP.Grammar284LeafParser
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Quoted (safe)

def render : Leaf → List Char
  | .node n => Grammar284NodeLeaf.render n
  | .op s => Shared.Beeping.NPcoNP.Grammar284OperationLeaf.render s.toList

def parse (input : List Char) : Option (Leaf × List Char) :=
  match Grammar284NodeLeaf.parse input with
  | some (n,tail) => some (.node n,tail)
  | none => (Shared.Beeping.NPcoNP.Grammar284OperationLeaf.parse input).map
      (fun (name, tail) => (.op (String.ofList name),tail))

def good : Leaf → Prop
  | .node _ => True
  | .op s => safe s.toList = true

theorem node_reject_op (name tail : List Char) :
    Grammar284NodeLeaf.parse (Shared.Beeping.NPcoNP.Grammar284OperationLeaf.render name ++ tail) = none := by
  rfl

theorem parse_render (leaf : Leaf) (tail : List Char) (h : good leaf) :
    parse (render leaf ++ tail) = some (leaf,tail) := by
  cases leaf with
  | node n =>
    simp [parse, render, Grammar284NodeLeaf.parse_render]
  | op s =>
    simp only [good] at h
    simp [parse, render, node_reject_op,
      Shared.Beeping.NPcoNP.Grammar284OperationLeaf.parse_render _ _ h]

end Shared.Beeping.NPcoNP.Grammar284LeafParser

namespace Shared.Beeping.NPcoNP.Grammar284LeafParser
open Shared.Beeping.NPcoNP.Grammar284

theorem render_eq_source_leaf (a : Leaf) :
    render a = Shared.Beeping.NPcoNP.Grammar284.SourceRender.leaf a := by
  cases a with
  | node n =>
    change Grammar284NodeLeaf.opening ++ Nat.toDigits 10 n ++ '\n' :: Grammar284NodeLeaf.suffix =
      "      {\n        \"node\": ".toList ++ (toString n).toList ++ "\n      }".toList
    rw [Nat.toString_eq_repr, Nat.toList_repr]
    rfl
  | op s =>
    rfl

end Shared.Beeping.NPcoNP.Grammar284LeafParser
