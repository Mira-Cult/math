import Shared.Beeping.NPcoNP.GrammarContractCert
import Shared.Beeping.NPcoNP.Grammar284NumberingData
import Shared.Beeping.NPcoNP.GraphCandidate284Data

/-! Finite kernel check: output indices 80–99. -/
namespace Shared.Beeping.NPcoNP.Grammar284ContractOutputShard04
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.GraphCandidate284
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem checked : contractCheckShard (contractRowCheck producerFullRows producerNumbering graph.rows) 80 20 = true := by decide
end Shared.Beeping.NPcoNP.Grammar284ContractOutputShard04
