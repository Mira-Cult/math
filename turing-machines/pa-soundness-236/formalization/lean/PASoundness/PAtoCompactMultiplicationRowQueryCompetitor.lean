import PASoundness.PAtoCompactMultiplicationRowQueryFirst

/-! Capture-safe row query for competitor coordinates 7 and 8 at the same
output 5. The row witness is alpha-freshened before queried names are
renamed. Both pair descriptions refer to the same outer edge, and the K
proof does not assume extensionality or unique pair representatives. This is
one pointwise component, not graph collection or multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationRowQueryCompetitor
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFixedFirstCoverageBase PASoundness.PAtoCompactFixedFirstRowWitnessAlpha
open PASoundness.PAtoCompactMultiplicationRowQueryFirst
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The same queried outer edge 63 represents the inner pair 18 and output 5,
and 18 represents the two competitor coordinates 7 and 8. -/
def competitorPairs : Formula := namedBoth (pairFormula 63 18 5) (pairFormula 18 7 8)
/-- A row competitor has the fixed major, a minor in the source, and the
corresponding edge of the same supplied map graph. -/
def competitorResult : Formula := namedBoth (.equal 7 30)
  (namedBoth (.member 31 8) (graphFormula 6 8 5))

private def F0 : Formula := .imp queryPairs (.imp freshRowWitness queryResult)
private def F1 : Formula := replace 3 7 F0
private def F2 : Formula := replace 4 8 F1

private def initial : KDerivation F0.encode := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [freshRowWitness.encode,queryPairs.encode]
  have hr : Context Γ freshRowWitness.encode := .head _ _
  have hq : Context Γ queryPairs.encode := .hypothesis (by simp [Γ])
  have ho : Context Γ (replace 9 63 rowWitness).encode := .mp hr (.closed row_witness_alpha.2)
  exact .mp ho (.mp hq (.closed row_query))

private def at7 : KDerivation F1.encode := by
  have hi := universalInstance 3 7 F0 (by decide) (by decide) (by decide)
  exact .mp (.generalize 3 initial) hi

private def at8 : KDerivation F2.encode := by
  have hi := universalInstance 4 8 F1 (by decide) (by decide) (by decide)
  exact .mp (.generalize 4 at7) hi

private theorem final_shape : F2 = .imp competitorPairs (.imp freshRowWitness competitorResult) := by decide

/-- From the row-branch classification and both descriptions of the same
outer edge, derive the competitor coordinates and the map edge. -/
def row_query_competitor : KDerivation (imp competitorPairs.encode
    (imp (replace 9 63 rowWitness).encode competitorResult.encode)) := by
  have h := at8
  rw [final_shape] at h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(replace 9 63 rowWitness).encode,competitorPairs.encode]
  have hr : Context Γ (replace 9 63 rowWitness).encode := .head _ _
  have hq : Context Γ competitorPairs.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ freshRowWitness.encode := .mp hr (.closed row_witness_alpha.1)
  exact .mp hf (.mp hq (.closed h))

theorem row_query_competitor_certificate : theoremCode (certificate row_query_competitor) =
    imp competitorPairs.encode (imp (replace 9 63 rowWitness).encode competitorResult.encode) :=
  certificate_correct row_query_competitor
end PASoundness.PAtoCompactMultiplicationRowQueryCompetitor
#print axioms PASoundness.PAtoCompactMultiplicationRowQueryCompetitor.row_query_competitor
#print axioms PASoundness.PAtoCompactMultiplicationRowQueryCompetitor.row_query_competitor_certificate
