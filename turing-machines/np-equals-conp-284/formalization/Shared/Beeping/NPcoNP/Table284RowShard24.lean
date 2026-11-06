import Shared.Beeping.NPcoNP.Table284RowCert
import Shared.Beeping.NPcoNP.Table284LineData

/-! Kernel-check a finite contiguous chunk of table rows. -/
namespace Shared.Beeping.NPcoNP.Table284RowShard24
open Table284Ascii.RowCert Table284LineData

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem checked : Chunk 284 240 lines24 pairs24 250 := by
  unfold lines24 pairs24
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
  exact Chunk.nil 250

end Shared.Beeping.NPcoNP.Table284RowShard24
