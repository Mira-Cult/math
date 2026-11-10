import PASoundness.PAtoCompactSegmentBackwardClosed
import PASoundness.PAtoCompactSegmentBackwardAll

/-! Quantified backward bijection for a supplied initial-segment filter.
Both outer transitivity, endpoint memberships, original matrix, filter, and
selected top edge remain explicit hypotheses. -/
namespace PASoundness.PAtoCompactSegmentBackwardFinal
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSegmentBackwardAll

/-- Every inner target has one unique preimage in the inner source through
the same supplied restricted graph. -/
def backward_all : KDerivation allGoal :=
  backward_all_of_point PAtoCompactSegmentBackwardClosed.backward_witness

theorem backward_all_certificate : theoremCode (certificate backward_all) = allGoal :=
  certificate_correct backward_all

end PASoundness.PAtoCompactSegmentBackwardFinal

#print axioms PASoundness.PAtoCompactSegmentBackwardFinal.backward_all
#print axioms PASoundness.PAtoCompactSegmentBackwardFinal.backward_all_certificate
