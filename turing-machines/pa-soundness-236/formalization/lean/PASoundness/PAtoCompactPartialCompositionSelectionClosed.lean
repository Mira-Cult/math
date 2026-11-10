import PASoundness.PAtoCompactPartialCompositionSelectionFamily
import PASoundness.PAtoCompactPartialCompositionGlobalStepClosed

/-! Candidate-source-restricted composition-graph selection and the resulting
literal K transitivity implication. The candidate guard is an object-level
hypothesis; this does not establish quotient congruence, arithmetic operations,
or PA proof transport. -/
namespace PASoundness.PAtoCompactPartialCompositionSelectionClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactConditionalTransitivitySelection
open PASoundness.PAtoCompactConditionalTransitivityWitnessInterface
open PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactPartialCompositionSelectionFamily
open PASoundness.PAtoCompactPartialCompositionGlobalStepClosed

/-- K derives the exact graph-selection condition under the explicit
source-candidate guard. -/
def candidate_graph_selection : KDerivation
    (imp (namedCandidate 0).encode graphSelection.encode) :=
  selection_family_of_step global_step

/-- The exact candidate-source guard implies transitivity of the concrete
order-isomorphism proposal. This does not assert any other quotient law. -/
def candidate_transitivity : KDerivation
    (imp (namedCandidate 0).encode (imp equivalentFormula.encode
      (imp secondEquivalent.encode targetEquivalent.encode))) :=
  compose candidate_graph_selection conditional_transitivity

theorem candidate_graph_selection_certificate :
    theoremCode (certificate candidate_graph_selection) =
      imp (namedCandidate 0).encode graphSelection.encode :=
  certificate_correct candidate_graph_selection

theorem candidate_transitivity_certificate :
    theoremCode (certificate candidate_transitivity) =
      imp (namedCandidate 0).encode (imp equivalentFormula.encode
        (imp secondEquivalent.encode targetEquivalent.encode)) :=
  certificate_correct candidate_transitivity

end PASoundness.PAtoCompactPartialCompositionSelectionClosed

#print axioms PASoundness.PAtoCompactPartialCompositionSelectionClosed.candidate_graph_selection
#print axioms PASoundness.PAtoCompactPartialCompositionSelectionClosed.candidate_transitivity
#print axioms PASoundness.PAtoCompactPartialCompositionSelectionClosed.candidate_transitivity_certificate
