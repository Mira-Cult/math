import Shared.Beeping.NPcoNP.Table284RowCert
import Shared.Beeping.NPcoNP.Table284LineData

/-! Kernel-check a finite contiguous chunk of table rows. -/
namespace Shared.Beeping.NPcoNP.Table284RowShard06
open Table284Ascii.RowCert Table284LineData

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem checked : Chunk 284 60 lines06 pairs06 70 := by
  unfold lines06 pairs06
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
  exact Chunk.nil 70

end Shared.Beeping.NPcoNP.Table284RowShard06
