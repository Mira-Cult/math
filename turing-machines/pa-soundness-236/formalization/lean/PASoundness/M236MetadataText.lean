import PASoundness.M236MetadataWitness
import PASoundness.M236MetadataNamesCheck
import PASoundness.M236Ascii

/-! Exact retained metadata file binding. The JSON file is not executed or
parsed by the integrity checker; Lean checks the embedded literal against the
witness and the graph-derived serializations. -/
set_option maxRecDepth 524288
set_option maxHeartbeats 0
namespace PASoundness.M236.Metadata
open PASoundness.M236.TextEncoding

def input : String := include_str ".." / ".." / "bindings" / "m236" / "producer-metadata.json"

/-- Exact embedded characters. Rebuild after changing this external input. -/
theorem input_chars :
    input = String.ofList (fileBytes.map fun b => Char.ofNat b.toNat) := by rfl

theorem ascii_checked : fileBytes.all (fun b => decide (b.toNat < 128)) = true := by decide

theorem input_checked : input.toByteArray = ⟨⟨fileBytes⟩⟩ := by
  rw [input_chars, String.toByteArray_ofList]
  apply PASoundness.M236.Ascii.encode_list
  intro b hb
  exact of_decide_eq_true ((List.all_eq_true.mp ascii_checked) b hb)

/-- The entire retained file is exactly the displayed concatenation. Its
three object bodies, root field and dispatcher summary are generated from the
Lean graph and state names; the other exact bytes remain as witness parts. -/
theorem binding : bytes input =
    part0 ++ List.intercalate separator grammarRows ++ part1 ++
    List.intercalate separator nameRows ++ part2 ++ bytes rootText ++ part3 ++
    List.intercalate separator stateRows ++ part4 ++ bytes dispatchText ++ part5 := by
  unfold bytes
  rw [input_checked]
  change fileBytes = _
  rw [assembled, grammar_rows, name_rows, state_rows, root_row, dispatch_row]
  rfl

end PASoundness.M236.Metadata
