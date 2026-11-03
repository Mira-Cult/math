import Shared.PNP.Record285.GrammarCoreGraphData

set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreGraph

/-- All 172 source graph rows agree with the literal grammar after finitely
many break/continue actions, including both outcomes of every test. -/
theorem producer_graph_checked : check producerRows producerPositions = true := by decide

end Shared.PNP.Record285.GrammarCoreGraph
