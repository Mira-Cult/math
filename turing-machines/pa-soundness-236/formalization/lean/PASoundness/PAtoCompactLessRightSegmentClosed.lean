import PASoundness.PAtoCompactLessRightSegmentTransport
import PASoundness.PAtoCompactLessRightSegmentAliases
import PASoundness.PAtoCompactSegmentMatrixClosed

/-! Constructive member transport and right-order substitution from the
proved arbitrary-segment restriction. The explicit object-level transitivity
and candidate guards are retained. No full quotient interpretation or PA
proof translation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLessRightSegmentClosed
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactQuotientOrder
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactLessRightWrapper

/-- Every member of the first outer domain has an E-equivalent member of the
second, under the displayed transitivity and represented-isomorphism guards. -/
def segment_transport : KDerivation
    (imp sourceTrans (imp targetTrans (imp (member 1 7)
      (imp E18.encode (existsCode 9 segmentBody9.encode))))) := by
  have h := PASoundness.PAtoCompactLessRightSegmentTransport.canonical_transport
    PASoundness.PAtoCompactSegmentMatrixClosed.segment_target
  exact PASoundness.PAtoCompactLessRightSegmentAliases.wrapper_segment h

theorem segment_transport_certificate : theoremCode (certificate segment_transport) =
    imp sourceTrans (imp targetTrans (imp (member 1 7)
      (imp E18.encode (existsCode 9 segmentBody9.encode)))) :=
  certificate_correct segment_transport

/-- Candidate-guarded substitutivity of the right argument of the concrete
quotient-order proposal, under transitivity of both represented right
endpoints. -/
def right_order_substitutivity : KDerivation
    (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp sourceTrans (imp targetTrans
        (imp E18.encode (imp lessFormula.encode targetLess.encode))))) :=
  right_order_of_segment segment_transport

theorem right_order_substitutivity_certificate :
    theoremCode (certificate right_order_substitutivity) =
      imp (candidateCode 0 37 32 33 34 30 35 10 36)
        (imp sourceTrans (imp targetTrans
          (imp E18.encode (imp lessFormula.encode targetLess.encode)))) :=
  certificate_correct right_order_substitutivity

end PASoundness.PAtoCompactLessRightSegmentClosed

#print axioms PASoundness.PAtoCompactLessRightSegmentClosed.segment_transport
#print axioms PASoundness.PAtoCompactLessRightSegmentClosed.segment_transport_certificate
#print axioms PASoundness.PAtoCompactLessRightSegmentClosed.right_order_substitutivity
#print axioms PASoundness.PAtoCompactLessRightSegmentClosed.right_order_substitutivity_certificate
