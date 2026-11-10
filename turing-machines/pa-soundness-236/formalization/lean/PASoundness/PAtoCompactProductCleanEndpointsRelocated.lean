import PASoundness.PAtoCompactProductCleanTripleEndpoints

/-! Capture-safe relocation of the old clean product domains to the names
used by the multiplication-row extension. This retains actual old graph10,
queried triple and clean-graph hypotheses. It does not infer cleanliness,
construct the row graph, or prove multiplication totality. -/
namespace PASoundness.PAtoCompactProductCleanEndpointsRelocated
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactProductCleanTripleEndpoints
open PASoundness.PAtoCompactProductCleanEndpointsPoint PASoundness.PAtoCompactOldTripleEdgeExtract
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact old-clean syntax used by the product-row case assumptions. -/
def oldCleanActual : Formula := replace 2 32 (replace 1 31 (replace 0 30 oldClean))
/-- The old queried coordinates belong to the relocated product domains. -/
def firstEndpoints : Formula := namedBoth (.member 30 3)
  (namedBoth (.member 31 4) (.member 32 5))
private def F0 : Formula := .imp oldClean (.imp oldTriple endpoints)
private def F1 : Formula := replace 0 30 F0
private def F2 : Formula := replace 1 31 F1
private def F3 : Formula := replace 2 32 F2

private def at30 : KDerivation F1.encode := by
  have hi := universalInstance 0 30 F0 (by decide) (by decide) (by decide)
  exact .mp (.generalize 0 triple_endpoints) hi
private def at31 : KDerivation F2.encode := by
  have hi := universalInstance 1 31 F1 (by decide) (by decide) (by decide)
  exact .mp (.generalize 1 at30) hi
private def at32 : KDerivation F3.encode := by
  have hi := universalInstance 2 32 F2 (by decide) (by decide) (by decide)
  exact .mp (.generalize 2 at31) hi

private theorem final_shape : F3 = .imp oldCleanActual (.imp oldTriple firstEndpoints) := by decide

/-- A queried triple in explicitly clean graph10 has the displayed
first-factor, second-factor and old-result memberships. -/
def first_endpoints : KDerivation (imp oldCleanActual.encode (imp oldTriple.encode firstEndpoints.encode)) := by
  have h := at32
  rw [final_shape] at h
  exact h

theorem first_endpoints_certificate : theoremCode (certificate first_endpoints) =
    imp oldCleanActual.encode (imp oldTriple.encode firstEndpoints.encode) := certificate_correct _
end PASoundness.PAtoCompactProductCleanEndpointsRelocated
#print axioms PASoundness.PAtoCompactProductCleanEndpointsRelocated.first_endpoints
#print axioms PASoundness.PAtoCompactProductCleanEndpointsRelocated.first_endpoints_certificate
