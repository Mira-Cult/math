import Shared.Beeping.NPcoNP.Grammar284NodePairs
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! Bridge the generic fixed-count node parser's renderer to the pinned
SourceRender layout. This does not assert any relation to source bytes. -/
namespace Shared.Beeping.NPcoNP.Grammar284NodePairsSource
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.SourceRender
open Shared.Beeping.NPcoNP.Grammar284NodePairs

theorem renderPair_eq_node (p : Leaf × Leaf) : renderPair leaf p = node p := by
  rfl

theorem renderNodes_eq_nodes_nonempty (xs : List (Leaf × Leaf)) (tail : List Char)
    (hne : xs ≠ []) : nodes xs tail = renderNodes leaf xs ++ '\n' :: tail := by
  induction xs with
  | nil => contradiction
  | cons p ps ih =>
    cases ps with
    | nil => simp [nodes, renderNodes, renderPair_eq_node]
    | cons q rest =>
      simp only [nodes, renderNodes, renderPair_eq_node]
      rw [ih (by simp)]
      simp [List.append_assoc, sepPair]

end Shared.Beeping.NPcoNP.Grammar284NodePairsSource
