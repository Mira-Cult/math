import Shared.Beeping.NPcoNP.GrammarContractCert
import Shared.Beeping.NPcoNP.Grammar284NumberingData
import Shared.Beeping.NPcoNP.GraphCandidate284Data

/-! Finite kernel check: target indices 60–79. -/
namespace Shared.Beeping.NPcoNP.Grammar284ContractTargetShard03
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.GraphCandidate284
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem checked : contractCheckShard (targetCheck producerFullRows producerNumbering.map) 60 20 = true := by decide
end Shared.Beeping.NPcoNP.Grammar284ContractTargetShard03
