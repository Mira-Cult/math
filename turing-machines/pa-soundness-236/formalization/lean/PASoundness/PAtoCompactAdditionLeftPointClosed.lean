import PASoundness.PAtoCompactAdditionLeftPointAssembly
import PASoundness.PAtoCompactAdditionTopSourceTransport

/-! A finite K source-point derivation for the unequal-top addition graph.
The graph, suffix adjunction and old bijection remain literal antecedents;
there is no assumed proof-data transport, no suffix-transitivity condition,
and no claim of the full quantified bijection or addition totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionLeftPointClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdditionOldSourceWitness PASoundness.PAtoCompactAdditionOldSourceClosed
open PASoundness.PAtoCompactAdditionTopWitnessUnequal PASoundness.PAtoCompactAdditionTopSourceTransport
open PASoundness.PAtoCompactAdditionLeftPointAssembly
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The source-point case with the equality transport explicitly constructed. -/
def source_point_closed : KDerivation (imp oldBijection.encode (imp oldClean.encode
    (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
      (imp (adjoinCode 34 32 40 41) (imp (successorCode 31 38 39)
        (imp (member 38 2) (existsCode 3 newBody.encode)))))))) := by
  apply source_point
  simpa [newBody,pointBody] using top_source_transport

theorem source_point_closed_certificate : theoremCode (certificate source_point_closed) =
    imp oldBijection.encode (imp oldClean.encode
      (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
        (imp (adjoinCode 34 32 40 41) (imp (successorCode 31 38 39)
          (imp (member 38 2) (existsCode 3 newBody.encode))))))) :=
  certificate_correct source_point_closed
end PASoundness.PAtoCompactAdditionLeftPointClosed
#print axioms PASoundness.PAtoCompactAdditionLeftPointClosed.source_point_closed
#print axioms PASoundness.PAtoCompactAdditionLeftPointClosed.source_point_closed_certificate
