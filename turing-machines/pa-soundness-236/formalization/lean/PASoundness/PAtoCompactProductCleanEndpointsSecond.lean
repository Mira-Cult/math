import PASoundness.PAtoCompactProductCleanEndpointsRelocated

/-! Capture-safe second-point specialization of the old-product endpoint
extraction. The explicit clean old graph is a hypothesis; raw product
matrices need not exclude garbage. This does not prove a product graph,
row collection, multiplication totality, or PA soundness. -/
namespace PASoundness.PAtoCompactProductCleanEndpointsSecond
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactOldTripleEdgeExtract PASoundness.PAtoCompactProductCleanEndpointsRelocated
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The old graph's product triple at queried point 7,8,9. -/
def secondTriple : Formula := replace 6 10 (tripleFormula 7 8 9)
/-- The corresponding old-domain membership guards. -/
def secondEndpoints : Formula := namedBoth (.member 30 7)
  (namedBoth (.member 31 8) (.member 32 9))

private def F0 : Formula := .imp oldCleanActual (.imp oldTriple firstEndpoints)
private def F1 : Formula := replace 3 7 F0
private def F2 : Formula := replace 4 8 F1
private def F3 : Formula := replace 5 9 F2

private def at7 : KDerivation F1.encode := by
  have h0 : KDerivation F0.encode := first_endpoints
  have hi := universalInstance 3 7 F0 (by decide) (by decide) (by decide)
  exact .mp (.generalize 3 h0) hi
private def at8 : KDerivation F2.encode := by
  have hi := universalInstance 4 8 F1 (by decide) (by decide) (by decide)
  exact .mp (.generalize 4 at7) hi
private def at9 : KDerivation F3.encode := by
  have hi := universalInstance 5 9 F2 (by decide) (by decide) (by decide)
  exact .mp (.generalize 5 at8) hi
private theorem final_shape : F3 = .imp oldCleanActual (.imp secondTriple secondEndpoints) := by decide

/-- An actual second-point triple in the same clean old graph has its three
old product endpoints in the displayed domains. -/
def second_endpoints : KDerivation (imp oldCleanActual.encode
    (imp secondTriple.encode secondEndpoints.encode)) := by
  have h := at9
  rw [final_shape] at h
  exact h

theorem second_endpoints_certificate : theoremCode (certificate second_endpoints) =
    imp oldCleanActual.encode (imp secondTriple.encode secondEndpoints.encode) := certificate_correct _
end PASoundness.PAtoCompactProductCleanEndpointsSecond
#print axioms PASoundness.PAtoCompactProductCleanEndpointsSecond.second_endpoints
#print axioms PASoundness.PAtoCompactProductCleanEndpointsSecond.second_endpoints_certificate
