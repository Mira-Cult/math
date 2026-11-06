import Shared.Beeping.NPcoNP.Table284RowCert
import Shared.Beeping.NPcoNP.Table284LineData

/-! Kernel-check a finite contiguous chunk of table rows. -/
namespace Shared.Beeping.NPcoNP.Table284RowShard28
open Table284Ascii.RowCert Table284LineData

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem checked : Chunk 284 280 lines28 pairs28 284 := by
  unfold lines28 pairs28
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  exact Chunk.nil 284

end Shared.Beeping.NPcoNP.Table284RowShard28
