import PASoundness.M236TableRowsRaw
import PASoundness.M236Ascii

set_option maxRecDepth 131072
set_option maxHeartbeats 0
namespace PASoundness.M236.TableTextRaw
open PASoundness.M236.TextEncoding PASoundness.M236.TableRowsRaw

def input : String := include_str ".." / ".." / "bindings" / "m236" / "raw.tm"

/-- The embedded file has exactly these characters. Recompile after changing
the external input; this is an equality, not a digest comparison. -/
theorem input_chars :
    input = String.ofList (fileBytes.map fun b => Char.ofNat b.toNat) := by rfl

theorem ascii_checked : fileBytes.all (fun b => decide (b.toNat < 128)) = true := by decide

theorem input_checked : input.toByteArray = ⟨⟨fileBytes⟩⟩ := by
  rw [input_chars, String.toByteArray_ofList]
  apply PASoundness.M236.Ascii.encode_list
  intro b hb
  exact of_decide_eq_true ((List.all_eq_true.mp ascii_checked) b hb)

/-- Exact retained file bytes equal the serialization of the Lean
machine, including every input, write, movement, target and event label. -/
theorem binding : bytes input = tableBytes raw rawLabels := by
  unfold bytes tableBytes
  rw [input_checked]
  change fileBytes = _
  rw [assembled, header_checked, rows_checked]

end PASoundness.M236.TableTextRaw
