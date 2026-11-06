import Shared.Beeping.NPcoNP.Source284SATReferenceFrame
import Shared.Beeping.NPcoNP.Source284TwoObligations
import Shared.Beeping.NPcoNP.Source284SATTableParameters
import Shared.Beeping.NPcoNP.Source284SATProducerIteration

/-! The 284 source controller with SAT semantics reduced to a concrete
finite-row construction cost. This is conditional on that cost and on
single-candidate coverage; it is not a literal-machine endpoint. -/
namespace Shared.Beeping.NPcoNP.Source284RowCostConditional

open ComplexityTheory
open Shared.Codes.FinitePrograms (Program)
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284Comparison

/-- The remaining assumptions are the canonical polynomial running time of
the specified row constructor and the single-candidate coverage theorem. -/
theorem entry_controller_iff_classes
    (rowCost : ∀ (program : Program) (clock : Polynomial Nat),
      IsPolyTime (Source284SATReferenceFrame.tableRows program clock))
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    (Shared.Beeping.CandidateEntryController.system compare 0).EventuallySilent ↔ NP = coNP :=
  Source284TwoObligations.entry_controller_iff_classes
    (Source284SATReferenceFrame.sat_hard_of_uniform_rows rowCost) coverage

/-- The uniform row-cost premise can itself be reduced to the canonical
polynomial-time bound for one explicitly defined finite-row producer. -/
theorem entry_controller_iff_of_producer
    (producerCost : IsPolyTime Source284SATTableParameters.produceRows)
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    (Shared.Beeping.CandidateEntryController.system compare 0).EventuallySilent ↔ NP = coNP :=
  entry_controller_iff_classes
    (Source284SATTableParameters.tableRows_isPolyTime_of_producer producerCost) coverage

/-- It is enough to establish the cost of one bounded row worker; the finite
range traversal and all other reduction costs have been proved separately. -/
theorem entry_controller_iff_of_bounded_worker
    (workerCost : IsPolyTime Source284SATProducerIteration.boundedRowWorker)
    (coverage : referenceLanguageᶜ ∈ NP →
      ∃ j, candidateLanguage j = referenceLanguageᶜ) :
    (Shared.Beeping.CandidateEntryController.system compare 0).EventuallySilent ↔ NP = coNP :=
  entry_controller_iff_of_producer
    (Source284SATProducerIteration.produceRows_isPolyTime_of_bounded_worker workerCost) coverage

end Shared.Beeping.NPcoNP.Source284RowCostConditional
