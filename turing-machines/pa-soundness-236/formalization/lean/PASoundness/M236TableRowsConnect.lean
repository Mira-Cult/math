import PASoundness.M236TableRowsSelected
import PASoundness.M236TableRowsRaw

/-! The generated witnesses serialize the Lean machines exactly. The separate
link from the retained files to these witnesses is not assumed here. -/
namespace PASoundness.M236.TableRowsConnect
open PASoundness.M236.TextEncoding

theorem selected_witness :
    TableRowsSelected.fileBytes = tableBytes machine machineLabels := by
  unfold tableBytes
  rw [TableRowsSelected.assembled, TableRowsSelected.header_checked,
    TableRowsSelected.rows_checked]

theorem raw_witness : TableRowsRaw.fileBytes = tableBytes raw rawLabels := by
  unfold tableBytes
  rw [TableRowsRaw.assembled, TableRowsRaw.header_checked, TableRowsRaw.rows_checked]

end PASoundness.M236.TableRowsConnect
