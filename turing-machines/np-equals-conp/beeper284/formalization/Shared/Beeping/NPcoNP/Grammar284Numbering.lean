import Shared.Beeping.NPcoNP.Grammar284NumberingData

/-! Exact numbering of the generated candidate full rows. This does not bind
those rows to producer bytes or establish the contraction target. -/
namespace Shared.Beeping.NPcoNP.Grammar284
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem producerNumbering_correct : number producerFullRows = producerNumbering := by rfl

theorem producerNumbering_nonempty : producerNumbering.kept.isEmpty = false := by rfl

theorem producerNumbering_size : producerNumbering.kept.size = 185 := by rfl

end Shared.Beeping.NPcoNP.Grammar284
