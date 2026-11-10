import PASoundness.M236MetadataWitness

/-! Exact object-boundary checks for the witness spans around the serialized
metadata fields. Together with `M236MetadataText.binding`, these identify the
positions of the graph-derived sections in the retained file. -/
set_option maxRecDepth 524288
set_option maxHeartbeats 0
namespace PASoundness.M236.Metadata
open PASoundness.M236.TextEncoding

theorem grammar_header : part0.drop 22901 = bytes "  \"grammar\": {\n" := by decide

theorem grammar_names_boundary : part1 =
    bytes "\n  },\n  \"grammar_depth\": 25,\n  \"grammar_names\": {\n" := by decide

theorem names_root_boundary : part2 = bytes "\n  },\n" := by decide

theorem state_header : part3.drop 323 = bytes "  \"named_state_to_id\": {\n" := by decide

theorem state_closing : part4.take 6 = bytes "\n  },\n" := by decide

end PASoundness.M236.Metadata
