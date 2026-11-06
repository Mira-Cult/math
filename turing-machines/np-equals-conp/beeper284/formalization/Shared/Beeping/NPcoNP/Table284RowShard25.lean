import Shared.Beeping.NPcoNP.Table284RowCert
import Shared.Beeping.NPcoNP.Table284LineData

/-! Kernel-check a finite contiguous chunk of table rows. -/
namespace Shared.Beeping.NPcoNP.Table284RowShard25
open Table284Ascii.RowCert Table284LineData

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem checked : Chunk 284 250 lines25 pairs25 260 := by
  unfold lines25 pairs25
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  refine Chunk.cons ?_ ?_
  · constructor <;> decide
  exact Chunk.nil 260

end Shared.Beeping.NPcoNP.Table284RowShard25
