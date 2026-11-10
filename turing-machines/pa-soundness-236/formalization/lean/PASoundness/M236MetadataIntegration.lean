import PASoundness.M236MetadataText
import PASoundness.M236MetadataBoundaries
import PASoundness.M236GrammarCodec

/-! The exact retained metadata text, graph rows, state labels and universal
finite-path facts in one reusable interface. This does not assert that the
producer source program compiles to the graph. -/
namespace PASoundness.M236.Metadata
open PASoundness.M236.TextEncoding PASoundness.M236.Grammar
open PASoundness.M236.UnaryAnchor

/-- Exact byte-level producer metadata binding and its checked literal-table
and return-counter consequences. The other metadata bytes remain explicit
witness spans. No general-purpose JSON parser is assumed. -/
theorem metadata_table_contract :
    bytes input =
      part0 ++ List.intercalate separator grammarRows ++ part1 ++
      List.intercalate separator nameRows ++ part2 ++ bytes rootText ++ part3 ++
      List.intercalate separator stateRows ++ part4 ++ bytes dispatchText ++ part5 ∧
    part0.drop 22901 = bytes "  \"grammar\": {\n" ∧
    part1 = bytes "\n  },\n  \"grammar_depth\": 25,\n  \"grammar_names\": {\n" ∧
    part2 = bytes "\n  },\n" ∧
    part3.drop 323 = bytes "  \"named_state_to_id\": {\n" ∧
    part4.take 6 = bytes "\n  },\n" ∧
    grammarOrder.Perm (List.finRange 158) ∧ stateOrder.Perm (List.finRange 237) ∧
    (∀ (i : Fin 158) (b : Bool),
      (raw.table.row nodes[i].state b, rawLabels.at nodes[i].state b) =
        expected nodes b (edge nodes i b)) ∧
    (∀ (i : Fin 158) (b : Bool), leafNamed i b) ∧
    nodes[157].state = 79 ∧ completePaths.length = 760 ∧
    (∀ (word : List Bool), LeafPath nodes 157 word →
      ∃ (runs : List (Fin 6)) (bit : Bool) (pcTail : List Bool),
        counterWord runs = ([true, true, false] ++ word).reverse ∧
        counterPush runs [] = true :: bit :: pcTail) := by
  exact ⟨binding, grammar_header, grammar_names_boundary, names_root_boundary,
    state_header, state_closing, grammar_order_complete, state_order_complete,
    literal_rows, leaf_names_checked, root_state, leaf_count, leaf_path_codec⟩

end PASoundness.M236.Metadata
