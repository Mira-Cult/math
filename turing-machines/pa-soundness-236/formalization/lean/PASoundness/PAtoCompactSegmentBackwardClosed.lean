import PASoundness.PAtoCompactSegmentBackwardAssembly
import PASoundness.PAtoCompactSegmentBackwardPoint
import PASoundness.PAtoCompactSegmentBackwardUnique

/-! Backward witness transfer for a supplied restriction of an isomorphism to
arbitrary inner segments. Both outer transitivity and all graph and endpoint
guards are explicit. This does not construct the filter or the full matrix. -/
namespace PASoundness.PAtoCompactSegmentBackwardClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSegmentBackwardAssembly

/-- Every supplied inner-target member has a unique represented preimage
in the inner source, using the same filtered graph. -/
def backward_witness : KDerivation fullGoal :=
  backward_witness_of_point_unique
    PAtoCompactSegmentBackwardPoint.backward_point
    PAtoCompactSegmentBackwardUnique.backward_unique

theorem backward_witness_certificate : theoremCode (certificate backward_witness) = fullGoal :=
  certificate_correct backward_witness

end PASoundness.PAtoCompactSegmentBackwardClosed

#print axioms PASoundness.PAtoCompactSegmentBackwardClosed.backward_witness
#print axioms PASoundness.PAtoCompactSegmentBackwardClosed.backward_witness_certificate
