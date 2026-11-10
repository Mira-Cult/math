import PASoundness.PAtoCompactRetainedZeroLeaf
import PASoundness.PAtoCompactZeroGraphOutputTransport

/-! The retained zero-substitution leaf with its zero-output transport
constructed as a finite K proof. No semantic soundness theorem is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRetainedZeroLeafClosed
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstInduction
open PASoundness.PAtoCompactRetainedZeroLeaf PASoundness.PAtoCompactZeroGraphOutputTransport

/-- Both term-graph directions under the retained zero graph and any guard.
Names q and out may coincide. -/
noncomputable def retained_zero_leaf_closed (g : Formula) (q d b out : Nat)
    (hqd : q < d) (hq : q < b) (hout : out < b) :
    Align (andF g (termGraph id Peano.zero q d)) (.var q) Peano.zero b out :=
  retained_zero_leaf g q d b out hqd hq hout (zero_graph_output id b q out hq hout)

end PASoundness.PAtoCompactRetainedZeroLeafClosed

#print axioms PASoundness.PAtoCompactRetainedZeroLeafClosed.retained_zero_leaf_closed
