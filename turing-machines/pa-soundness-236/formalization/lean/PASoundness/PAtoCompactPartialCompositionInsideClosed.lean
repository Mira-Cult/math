import PASoundness.PAtoCompactPartialCompositionInsideWitness
import PASoundness.PAtoCompactPartialCompositionSelectedElim
import PASoundness.PAtoCompactPartialCompositionOldGraphElim
import PASoundness.PAtoCompactCompositionForwardAll
import PASoundness.PAtoCompactPartialCompositionBackwardAll

/-! The inside-source successor step for the partial-composition invariant.
Selected middle/output, pair, old and new graph witnesses are all eliminated.
Both original bijections, the successor graph, and source membership remain
explicit object-level hypotheses. The outside-source branch, induction and
arbitrary composition-graph collection remain separate. -/
namespace PASoundness.PAtoCompactPartialCompositionInsideClosed
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactConditionalTransitivityEdgeForward
open PASoundness.PAtoCompactPartialCompositionBase PASoundness.PAtoCompactPartialCompositionInsideWitness
open PASoundness.PAtoCompactPartialCompositionSelectedElim PASoundness.PAtoCompactPartialCompositionOldGraphElim
open PASoundness.PAtoCompactCompositionForwardAll PASoundness.PAtoCompactPartialCompositionBackwardAll

/-- At an endpoint within the source, an existing partial-composition graph
extends through the supplied prefix successor. -/
def inside_successor_closed : KDerivation
    (imp bijectionFormula.encode (imp secondBijection.encode (imp (successorCode 10 13 15)
      (imp (member 0 10) (imp (existsCode 9 partialComposition.encode)
        (existsCode 9 (replace 10 13 partialComposition).encode)))))) :=
  eliminate_old_graph (eliminate_selected (inside_witness forward_all backward_all_from_premises))

theorem inside_successor_closed_certificate : theoremCode (certificate inside_successor_closed) =
    imp bijectionFormula.encode (imp secondBijection.encode (imp (successorCode 10 13 15)
      (imp (member 0 10) (imp (existsCode 9 partialComposition.encode)
        (existsCode 9 (replace 10 13 partialComposition).encode))))) :=
  certificate_correct inside_successor_closed

end PASoundness.PAtoCompactPartialCompositionInsideClosed

#print axioms PASoundness.PAtoCompactPartialCompositionInsideClosed.inside_successor_closed
#print axioms PASoundness.PAtoCompactPartialCompositionInsideClosed.inside_successor_closed_certificate
