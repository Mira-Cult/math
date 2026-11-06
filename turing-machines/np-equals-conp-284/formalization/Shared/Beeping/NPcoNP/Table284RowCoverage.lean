import Shared.Beeping.NPcoNP.Table284RowShard00
import Shared.Beeping.NPcoNP.Table284RowShard01
import Shared.Beeping.NPcoNP.Table284RowShard02
import Shared.Beeping.NPcoNP.Table284RowShard03
import Shared.Beeping.NPcoNP.Table284RowShard04
import Shared.Beeping.NPcoNP.Table284RowShard05
import Shared.Beeping.NPcoNP.Table284RowShard06
import Shared.Beeping.NPcoNP.Table284RowShard07
import Shared.Beeping.NPcoNP.Table284RowShard08
import Shared.Beeping.NPcoNP.Table284RowShard09
import Shared.Beeping.NPcoNP.Table284RowShard10
import Shared.Beeping.NPcoNP.Table284RowShard11
import Shared.Beeping.NPcoNP.Table284RowShard12
import Shared.Beeping.NPcoNP.Table284RowShard13
import Shared.Beeping.NPcoNP.Table284RowShard14
import Shared.Beeping.NPcoNP.Table284RowShard15
import Shared.Beeping.NPcoNP.Table284RowShard16
import Shared.Beeping.NPcoNP.Table284RowShard17
import Shared.Beeping.NPcoNP.Table284RowShard18
import Shared.Beeping.NPcoNP.Table284RowShard19
import Shared.Beeping.NPcoNP.Table284RowShard20
import Shared.Beeping.NPcoNP.Table284RowShard21
import Shared.Beeping.NPcoNP.Table284RowShard22
import Shared.Beeping.NPcoNP.Table284RowShard23
import Shared.Beeping.NPcoNP.Table284RowShard24
import Shared.Beeping.NPcoNP.Table284RowShard25
import Shared.Beeping.NPcoNP.Table284RowShard26
import Shared.Beeping.NPcoNP.Table284RowShard27
import Shared.Beeping.NPcoNP.Table284RowShard28

/-! Row coverage for the generated line data, not yet a
binding of those lines to the preserved source characters. -/
namespace Shared.Beeping.NPcoNP.Table284RowCoverage
open Table284Ascii.RowCert Table284LineData

set_option maxRecDepth 8192

theorem chunk : Chunk 284 0 lines pairs 284 := by
  unfold lines pairs
  simp only [List.append_assoc]
  exact Chunk.append Table284RowShard00.checked (Chunk.append Table284RowShard01.checked (Chunk.append Table284RowShard02.checked (Chunk.append Table284RowShard03.checked (Chunk.append Table284RowShard04.checked (Chunk.append Table284RowShard05.checked (Chunk.append Table284RowShard06.checked (Chunk.append Table284RowShard07.checked (Chunk.append Table284RowShard08.checked (Chunk.append Table284RowShard09.checked (Chunk.append Table284RowShard10.checked (Chunk.append Table284RowShard11.checked (Chunk.append Table284RowShard12.checked (Chunk.append Table284RowShard13.checked (Chunk.append Table284RowShard14.checked (Chunk.append Table284RowShard15.checked (Chunk.append Table284RowShard16.checked (Chunk.append Table284RowShard17.checked (Chunk.append Table284RowShard18.checked (Chunk.append Table284RowShard19.checked (Chunk.append Table284RowShard20.checked (Chunk.append Table284RowShard21.checked (Chunk.append Table284RowShard22.checked (Chunk.append Table284RowShard23.checked (Chunk.append Table284RowShard24.checked (Chunk.append Table284RowShard25.checked (Chunk.append Table284RowShard26.checked (Chunk.append Table284RowShard27.checked (Table284RowShard28.checked))))))))))))))))))))))))))))

theorem parsed_rows : Table284Ascii.rows 284 0 (lines ++ [[]]) =
    some Table284.data.2 := by
  simpa only [pairs_eq_data] using rows_complete 284 0 lines pairs chunk

end Shared.Beeping.NPcoNP.Table284RowCoverage
