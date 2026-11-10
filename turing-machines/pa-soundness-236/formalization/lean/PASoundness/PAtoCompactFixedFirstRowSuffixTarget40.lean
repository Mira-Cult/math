import PASoundness.PAtoCompactFixedFirstRowClosed
import PASoundness.PAtoCompactTransitiveDomain
import PASoundness.PAtoCompactPredecessor
import PASoundness.PAtoCompactLeastCounterexample

/-! Capture-safe change of the supplied row-map target label from 32 to 40.
This does not select a clean map or establish a multiplication product. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstRowSuffixTarget40
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactFixedFirstRestrictedInduction PASoundness.PAtoCompactFixedFirstRowClosed
open PASoundness.PAtoCompactMultiplicationRowMapEdge
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def C : Formula :=
  namedBoth (namedBoth (namedTransitive 31 209 210) (namedMembersTransitive 31 213 209 210))
    (namedBoth (.all 202 (namedGreatestSubsetsBody 31 202 0 205 206))
      (.all 202 (namedLeastSubsetsBody 31 202 0 203 205 206)))

private theorem C_code : C.encode = candidateCode 31 213 209 210 202 0 203 205 206 := by rfl

private def stmt : Formula := .imp C (.imp mapBijection (replace 0 31 predicate))

/-- The exact graph-6 bijection between source 31 and target 40. -/
def mapBijection40 : Formula := replace 1 40 (replace 0 31 bijectionFormula)

/-- Changing the map target leaves both the candidate guard and the row
predicate untouched, including the existential row graph and original graph. -/
def row_exists_at_40 : KDerivation
    (imp (candidateCode 31 213 209 210 202 0 203 205 206)
      (imp mapBijection40.encode (replace 0 31 predicate).encode)) := by
  have h : KDerivation stmt.encode := by
    simpa only [stmt, Formula.encode, C_code] using row_exists
  have hi := universalInstance 32 40 stmt (by decide) (by decide) (by decide)
  have h' := KDerivation.mp (.generalize 32 h) hi
  have he : replace 32 40 stmt = .imp C (.imp mapBijection40 (replace 0 31 predicate)) := by decide
  rw [he] at h'
  simpa only [Formula.encode, C_code] using h'

theorem row_exists_at_40_certificate : theoremCode (certificate row_exists_at_40) =
    imp (candidateCode 31 213 209 210 202 0 203 205 206)
      (imp mapBijection40.encode (replace 0 31 predicate).encode) := certificate_correct _
end PASoundness.PAtoCompactFixedFirstRowSuffixTarget40
#print axioms PASoundness.PAtoCompactFixedFirstRowSuffixTarget40.mapBijection40
#print axioms PASoundness.PAtoCompactFixedFirstRowSuffixTarget40.row_exists_at_40
#print axioms PASoundness.PAtoCompactFixedFirstRowSuffixTarget40.row_exists_at_40_certificate
