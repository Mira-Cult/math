import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.CompactNamed
import PASoundness.PAtoCompactZeroSuccessor

/-! Literal K extraction of the inner pair and outer graph-member witnesses
from one old product triple. The same outer object is retained in membership
and pair formulas. This does not construct the graph, infer any endpoint
guards, assume extensionality, or prove multiplication totality. -/
namespace PASoundness.PAtoCompactOldTripleEdgeExtract
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The literal triple of old graph 10 at the first queried tuple. -/
def oldTriple : Formula := replace 6 10 (tripleFormula 3 4 5)
/-- The retained inner pair and actual old-graph member. -/
def coords : Formula := pairFormula 18 3 4
def outerBody : Formula := namedBoth (.member 10 19) (pairFormula 19 18 5)
def expandedTriple : Formula := .ex 18 (.ex 19 (namedBoth coords outerBody))

theorem old_shape : oldTriple = .ex 18 (namedBoth coords (.ex 19 outerBody)) := by decide

private def pairing : KDerivation (imp coords.encode (imp outerBody.encode
    (namedBoth coords outerBody).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [outerBody.encode,coords.encode]
  have ha : Context Γ coords.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ outerBody.encode := .head _ _
  simpa [namedBoth,Formula.not,Formula.encode,both,neg] using Context.conjunctionIntro ha hb

private def inside : KDerivation (imp (namedBoth coords (.ex 19 outerBody)).encode
    (existsCode 19 (namedBoth coords outerBody).encode)) := by
  have h := conditionalExistsCongr 19 (coords.vacuity 19 (by decide)) pairing
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(namedBoth coords (.ex 19 outerBody)).encode]
  have hb : Context Γ (both coords.encode (existsCode 19 outerBody.encode)) := by
    have hi : Context Γ (namedBoth coords (.ex 19 outerBody)).encode := .head _ _
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using hi
  exact .mp (Context.conjunctionRight hb) (.mp (Context.conjunctionLeft hb) (.closed h))

/-- An actual old triple yields both pair descriptions and membership of the
same outer edge in graph 10. -/
def triple_to_expanded : KDerivation (imp oldTriple.encode expandedTriple.encode) := by
  have h := existsCongr 18 inside
  rw [old_shape]
  simpa [expandedTriple,Formula.encode] using h

theorem triple_to_expanded_certificate : theoremCode (certificate triple_to_expanded) =
    imp oldTriple.encode expandedTriple.encode := certificate_correct _
end PASoundness.PAtoCompactOldTripleEdgeExtract
#print axioms PASoundness.PAtoCompactOldTripleEdgeExtract.triple_to_expanded
#print axioms PASoundness.PAtoCompactOldTripleEdgeExtract.triple_to_expanded_certificate
