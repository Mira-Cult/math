import PASoundness.PAtoCompactFixedFirstMapEdgeElim
import PASoundness.PAtoCompactFixedFirstInsideWitnessClosed

/-! Closed inside-index graph successor step from a supplied F bijection.
The F-edge and nested pair/graph witnesses are constructed inside K. This is
one branch of a row induction, not full graph collection or multiplication. -/
namespace PASoundness.PAtoCompactFixedFirstInsideMapClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.PAtoCompactMultiplicationRowMapEdge PASoundness.PAtoCompactFixedFirstMapEdgeElim

/-- From the supplied F bijection, a successor prefix, its inside-domain
condition, and an old invariant, K constructs a successor-prefix graph. -/
def inside_from_bijection : KDerivation (imp mapBijection.encode
    (imp (successorCode 0 1 2) (imp (member 31 0)
      (imp (rowInvariantPreserved 7).encode target.encode)))) := by
  apply inside_from_map
  change KDerivation (imp (successorCode 0 1 2) (imp (member 31 0)
    (imp (rowInvariantPreserved 7).encode (imp (PASoundness.PAtoCompactOrderIsomorphism.graphFormula 6 0 4).encode
      (existsCode 11 (replace 0 1 (rowInvariantPreserved 11)).encode)))))
  exact PASoundness.PAtoCompactFixedFirstInsideWitnessClosed.inside_witness

theorem inside_from_bijection_certificate : theoremCode (certificate inside_from_bijection) =
    imp mapBijection.encode (imp (successorCode 0 1 2)
      (imp (member 31 0) (imp (rowInvariantPreserved 7).encode target.encode))) :=
  certificate_correct inside_from_bijection
end PASoundness.PAtoCompactFixedFirstInsideMapClosed
#print axioms PASoundness.PAtoCompactFixedFirstInsideMapClosed.inside_from_bijection
#print axioms PASoundness.PAtoCompactFixedFirstInsideMapClosed.inside_from_bijection_certificate
