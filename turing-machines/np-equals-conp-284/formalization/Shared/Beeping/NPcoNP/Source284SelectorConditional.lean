import Shared.Beeping.NPcoNP.Source284SATWorkerSelect
import Shared.Beeping.NPcoNP.Source284RowCostConditional

/-! Exact remaining source-side obligations for the atomic controller.
This does not assert correctness of the physical 284-state machine. -/
namespace Shared.Beeping.NPcoNP.Source284SelectorConditional

open ComplexityTheory
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284Comparison

/-- Equality here is between explicit total functions on all encoded row
requests. The coverage premise concerns the source's coupled candidate index
and clock. Neither premise asserts the complexity equality itself. -/
theorem entry_controller_iff_classes
    (rows : Source284SATWorkerSelect.select = Source284SATProducerIteration.boundedRowWorker)
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    (Shared.Beeping.CandidateEntryController.system compare 0).EventuallySilent ↔ NP = coNP :=
  Source284RowCostConditional.entry_controller_iff_of_bounded_worker
    (Source284SATWorkerSelect.boundedRowWorker_isPolyTime_of_eq rows) coverage

end Shared.Beeping.NPcoNP.Source284SelectorConditional
