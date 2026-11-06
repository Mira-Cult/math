import Shared.Beeping.NPcoNP.ExpansionTrace.Final
import Shared.Beeping.NPcoNP.Grammar284FullRows
import Shared.Beeping.NPcoNP.GrammarFullGraphRowCheck

/-! Kernel check for full expansion row indices 260 through 269. -/
namespace Shared.Beeping.NPcoNP.GrammarFullRowsShard26
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem checked : indexedRowShard traceState557.acc producerFullRows 260 10 = true := by decide

end Shared.Beeping.NPcoNP.GrammarFullRowsShard26
