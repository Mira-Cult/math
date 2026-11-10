import PASoundness.PAtoCompactPartialCompositionInsideClosed
import PASoundness.PAtoCompactPartialCompositionOutsidePredicate

/-! Capture-safe induction-predicate alignment for the inside-source
partial-composition successor branch. Both supplied bijections, successor graph,
and source membership remain literal K antecedents. This does not establish
the outside case, global induction, or composition graph collection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionInsidePredicate
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactConditionalTransitivityEdgeForward
open PASoundness.PAtoCompactPartialCompositionPredicate
open PASoundness.PAtoCompactPartialCompositionOutsidePredicate
open PASoundness.PAtoCompactPartialCompositionInsideClosed

/-- At an endpoint in the source, the exact induction predicate advances to
its successor instance under the two supplied actual bijections. -/
def inside_predicate_step : KDerivation
    (imp bijectionFormula.encode (imp secondBijection.encode (imp (successorCode 10 13 15)
      (imp (member 0 10) (imp (replace 30 10 predicate).encode
        (replace 30 13 predicate).encode))))) := by
  rw [instance_roundtrip, successor_instance]
  exact inside_successor_closed

theorem inside_predicate_step_certificate : theoremCode (certificate inside_predicate_step) =
    imp bijectionFormula.encode (imp secondBijection.encode (imp (successorCode 10 13 15)
      (imp (member 0 10) (imp (replace 30 10 predicate).encode
        (replace 30 13 predicate).encode)))) :=
  certificate_correct inside_predicate_step

end PASoundness.PAtoCompactPartialCompositionInsidePredicate

#print axioms PASoundness.PAtoCompactPartialCompositionInsidePredicate.inside_predicate_step
#print axioms PASoundness.PAtoCompactPartialCompositionInsidePredicate.inside_predicate_step_certificate
