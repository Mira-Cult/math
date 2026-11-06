import Shared.Beeping.NPcoNP.Grammar284Numbering
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard00
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard01
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard02
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard03
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard04
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard05
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard06
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard07
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard08
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard09
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard10
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard11
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard12
import Shared.Beeping.NPcoNP.Grammar284ContractTargetShard13
import Shared.Beeping.NPcoNP.Grammar284ContractOutputShard00
import Shared.Beeping.NPcoNP.Grammar284ContractOutputShard01
import Shared.Beeping.NPcoNP.Grammar284ContractOutputShard02
import Shared.Beeping.NPcoNP.Grammar284ContractOutputShard03
import Shared.Beeping.NPcoNP.Grammar284ContractOutputShard04
import Shared.Beeping.NPcoNP.Grammar284ContractOutputShard05
import Shared.Beeping.NPcoNP.Grammar284ContractOutputShard06
import Shared.Beeping.NPcoNP.Grammar284ContractOutputShard07
import Shared.Beeping.NPcoNP.Grammar284ContractOutputShard08
import Shared.Beeping.NPcoNP.Grammar284ContractOutputShard09

/-! The complete staged contraction check for the candidate arrays.
This still does not bind the input rows to the producer grammar or bytes. -/
namespace Shared.Beeping.NPcoNP.Grammar284ContractCoverage
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.GraphCandidate284
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem fullRows_size : producerFullRows.size = 279 := by rfl

theorem allTargets : ∀ i < producerFullRows.size, (targetCheck producerFullRows producerNumbering.map) i = true := by
  intro i hi
  rw [fullRows_size] at hi
  by_cases h0 : i < 20
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 0 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard00.checked (by omega) (by omega)
  by_cases h20 : i < 40
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 20 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard01.checked (by omega) (by omega)
  by_cases h40 : i < 60
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 40 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard02.checked (by omega) (by omega)
  by_cases h60 : i < 80
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 60 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard03.checked (by omega) (by omega)
  by_cases h80 : i < 100
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 80 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard04.checked (by omega) (by omega)
  by_cases h100 : i < 120
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 100 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard05.checked (by omega) (by omega)
  by_cases h120 : i < 140
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 120 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard06.checked (by omega) (by omega)
  by_cases h140 : i < 160
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 140 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard07.checked (by omega) (by omega)
  by_cases h160 : i < 180
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 160 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard08.checked (by omega) (by omega)
  by_cases h180 : i < 200
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 180 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard09.checked (by omega) (by omega)
  by_cases h200 : i < 220
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 200 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard10.checked (by omega) (by omega)
  by_cases h220 : i < 240
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 220 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard11.checked (by omega) (by omega)
  by_cases h240 : i < 260
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 240 20 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard12.checked (by omega) (by omega)
  by_cases h260 : i < 279
  · exact contractCheckShard_sound (targetCheck producerFullRows producerNumbering.map) 260 19 i Shared.Beeping.NPcoNP.Grammar284ContractTargetShard13.checked (by omega) (by omega)
  omega

theorem allOutputs : ∀ i < producerNumbering.kept.size, (contractRowCheck producerFullRows producerNumbering graph.rows) i = true := by
  intro i hi
  rw [producerNumbering_size] at hi
  by_cases h0 : i < 20
  · exact contractCheckShard_sound (contractRowCheck producerFullRows producerNumbering graph.rows) 0 20 i Shared.Beeping.NPcoNP.Grammar284ContractOutputShard00.checked (by omega) (by omega)
  by_cases h20 : i < 40
  · exact contractCheckShard_sound (contractRowCheck producerFullRows producerNumbering graph.rows) 20 20 i Shared.Beeping.NPcoNP.Grammar284ContractOutputShard01.checked (by omega) (by omega)
  by_cases h40 : i < 60
  · exact contractCheckShard_sound (contractRowCheck producerFullRows producerNumbering graph.rows) 40 20 i Shared.Beeping.NPcoNP.Grammar284ContractOutputShard02.checked (by omega) (by omega)
  by_cases h60 : i < 80
  · exact contractCheckShard_sound (contractRowCheck producerFullRows producerNumbering graph.rows) 60 20 i Shared.Beeping.NPcoNP.Grammar284ContractOutputShard03.checked (by omega) (by omega)
  by_cases h80 : i < 100
  · exact contractCheckShard_sound (contractRowCheck producerFullRows producerNumbering graph.rows) 80 20 i Shared.Beeping.NPcoNP.Grammar284ContractOutputShard04.checked (by omega) (by omega)
  by_cases h100 : i < 120
  · exact contractCheckShard_sound (contractRowCheck producerFullRows producerNumbering graph.rows) 100 20 i Shared.Beeping.NPcoNP.Grammar284ContractOutputShard05.checked (by omega) (by omega)
  by_cases h120 : i < 140
  · exact contractCheckShard_sound (contractRowCheck producerFullRows producerNumbering graph.rows) 120 20 i Shared.Beeping.NPcoNP.Grammar284ContractOutputShard06.checked (by omega) (by omega)
  by_cases h140 : i < 160
  · exact contractCheckShard_sound (contractRowCheck producerFullRows producerNumbering graph.rows) 140 20 i Shared.Beeping.NPcoNP.Grammar284ContractOutputShard07.checked (by omega) (by omega)
  by_cases h160 : i < 180
  · exact contractCheckShard_sound (contractRowCheck producerFullRows producerNumbering graph.rows) 160 20 i Shared.Beeping.NPcoNP.Grammar284ContractOutputShard08.checked (by omega) (by omega)
  by_cases h180 : i < 185
  · exact contractCheckShard_sound (contractRowCheck producerFullRows producerNumbering graph.rows) 180 5 i Shared.Beeping.NPcoNP.Grammar284ContractOutputShard09.checked (by omega) (by omega)
  omega

theorem producerEntry : target producerFullRows producerNumbering.map
    (producerFullRows.size+1) 0 = some graph.entry := by rfl

theorem producerOutputSize : producerNumbering.kept.size = graph.rows.size := by rfl

theorem producerContract : contract producerFullRows = some graph := by
  exact contract_of_checked producerFullRows producerNumbering graph
    producerNumbering_correct producerNumbering_nonempty allTargets producerEntry
    producerOutputSize allOutputs

/-- A disconnected administrative self-loop still causes rejection. -/
example : contract #[⟨"beep", [0]⟩, ⟨"jump", [1]⟩] = none := by decide

end Shared.Beeping.NPcoNP.Grammar284ContractCoverage
