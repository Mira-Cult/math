import PASoundness.PAtoCompactMultiplicationOldNewCaseAdapter
import PASoundness.PAtoCompactProductCleanEndpointsRelocated

/-! The old/new lexicographic point case under the explicit shared context.
Old-graph hygiene and the new-row branch are object-level assumptions; the
finite K proof has no old-endpoint proof-data parameter. This is not a full
product graph or multiplication totality theorem. -/
namespace PASoundness.PAtoCompactMultiplicationOldNewCaseClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationFourCaseLex PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactMultiplicationOldNewCaseAdapter
attribute [local irreducible] imp PASoundness.Cantor.pair PASoundness.Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Clean graph10 supplies old coordinates, and the actual new-row witness
and clean suffix graph supply the new point. -/
def old_new_case : KDerivation
    (imp sharedPremise.encode (imp oldFirst (imp newSecond comparisons))) := by
  have h : KDerivation (imp oldCleanActual.encode (imp oldFirst
      (both (member 30 3) (both (member 31 4) (member 32 5))))) := by
    simpa [oldCleanActual, PAtoCompactProductCleanEndpointsRelocated.oldCleanActual,
      PAtoCompactProductCleanTripleEndpoints.oldClean, oldFirst,
      PAtoCompactMultiplicationOldTripleIntro.oldTriple,
      PAtoCompactOldTripleEdgeExtract.oldTriple,
      PAtoCompactProductCleanEndpointsRelocated.firstEndpoints,
      namedBoth,Formula.not,Formula.encode,both,neg] using
      PAtoCompactProductCleanEndpointsRelocated.first_endpoints
  exact old_new_from_endpoint h

theorem old_new_case_certificate : theoremCode (certificate old_new_case) =
    imp sharedPremise.encode (imp oldFirst (imp newSecond comparisons)) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationOldNewCaseClosed
#print axioms PASoundness.PAtoCompactMultiplicationOldNewCaseClosed.old_new_case
#print axioms PASoundness.PAtoCompactMultiplicationOldNewCaseClosed.old_new_case_certificate
