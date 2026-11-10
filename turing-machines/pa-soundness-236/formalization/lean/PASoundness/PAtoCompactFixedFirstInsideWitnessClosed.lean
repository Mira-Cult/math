import PASoundness.PAtoCompactFixedFirstInsideWitnessElim
import PASoundness.PAtoCompactFixedFirstInsideInvariantStep

/-! A finite K inside-index row-graph successor step. Given the displayed
source F-edge, it constructs and eliminates the nested pair and graph
witnesses and returns a graph satisfying the successor-prefix invariant.
This does not prove existence of the source F-edge, total row collection,
multiplication totality or PA soundness. -/
namespace PASoundness.PAtoCompactFixedFirstInsideWitnessClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFixedFirstPreservedBase

/-- No pair, graph-adjunction or inside-invariant proof-data inputs remain;
the source F-edge and inside-index membership are explicit antecedents. -/
def inside_witness : KDerivation (imp (successorCode 0 1 2) (imp (member 31 0)
    (imp (rowInvariantPreserved 7).encode (imp (graphFormula 6 0 4).encode
      (existsCode 11 (replace 0 1 (rowInvariantPreserved 11)).encode))))) := by
  apply PAtoCompactFixedFirstInsideWitnessElim.from_step
  simpa [PAtoCompactPointAdjoin.namedAdjoin, namedBoth, namedEither,
    Formula.not, Formula.encode, PAtoCompactPointAdjoin.adjoinCode, both, neg, either] using
    PAtoCompactFixedFirstInsideInvariantStep.inside_invariant

theorem inside_witness_certificate : theoremCode (certificate inside_witness) =
    imp (successorCode 0 1 2) (imp (member 31 0)
      (imp (rowInvariantPreserved 7).encode (imp (graphFormula 6 0 4).encode
        (existsCode 11 (replace 0 1 (rowInvariantPreserved 11)).encode)))) :=
  certificate_correct inside_witness
end PASoundness.PAtoCompactFixedFirstInsideWitnessClosed
#print axioms PASoundness.PAtoCompactFixedFirstInsideWitnessClosed.inside_witness
#print axioms PASoundness.PAtoCompactFixedFirstInsideWitnessClosed.inside_witness_certificate
