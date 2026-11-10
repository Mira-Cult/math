import PASoundness.M236MetadataText

/-! Positive and negative controls for the graph-derived metadata rows and
named literal states. These checks do not prove source-program correctness. -/
namespace PASoundness.M236.Metadata.Fixtures
open PASoundness.M236.Metadata

example : grammarItem 0 = "    \"0\": [\n      \"3.scratch.copy.inc\",\n      \"_continue.3\"\n    ]" := by decide
example : grammarItem 0 ≠ "    \"0\": [\n      \"_continue.3\",\n      \"3.scratch.copy.inc\"\n    ]" := by decide
example : nameItem 157 = "    \"157\": \"main().0\"" := by decide
example : stateNames[79] = "main().0" := by decide
example : stateNames[79] ≠ "6.break.0" := by decide
example : resolvedLeaf "emit.0" false = "6.continue.0" := by decide
example : leafEvent "emit.0" ≠ some true := by decide

end PASoundness.M236.Metadata.Fixtures
