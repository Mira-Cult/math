import Shared.Beeping.NPcoNP.Source284SATWorkerSelectCases
import Shared.Beeping.NPcoNP.Source284SelectorConditional

/-! The explicit selector closes the polynomial row-construction and SAT
hardness obligations. Candidate coverage and physical refinement remain
separate; no table-level endpoint is asserted. -/
namespace Shared.Beeping.NPcoNP.Source284SelectorClosed

open ComplexityTheory
open Shared.Codes.FinitePrograms (Program)
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284Comparison

theorem boundedRowWorker_isPolyTime :
    IsPolyTime Source284SATProducerIteration.boundedRowWorker :=
  Source284SATWorkerSelect.boundedRowWorker_isPolyTime_of_eq
    Source284SATWorkerSelect.select_eq_boundedRowWorker

theorem produceRows_isPolyTime : IsPolyTime Source284SATTableParameters.produceRows :=
  Source284SATProducerIteration.produceRows_isPolyTime_of_bounded_worker boundedRowWorker_isPolyTime

theorem tableRows_isPolyTime (program : Program) (clock : Polynomial Nat) :
    IsPolyTime (Source284SATReferenceFrame.tableRows program clock) :=
  Source284SATTableParameters.tableRows_isPolyTime_of_producer produceRows_isPolyTime program clock

theorem sat_hard :
    Shared.ComplexityBridge.CanonicalClasses.PolyRed Shared.ComplexityBridge.CNF.sat referenceLanguage :=
  Source284SATReferenceFrame.sat_hard_of_uniform_rows tableRows_isPolyTime

/-- This concerns the atomic comparison controller, with a single remaining
source-model coverage hypothesis. It is not the 284-state machine theorem. -/
theorem entry_controller_iff_classes
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    (Shared.Beeping.CandidateEntryController.system compare 0).EventuallySilent ↔ NP = coNP :=
  Source284SelectorConditional.entry_controller_iff_classes
    Source284SATWorkerSelect.select_eq_boundedRowWorker coverage

end Shared.Beeping.NPcoNP.Source284SelectorClosed
