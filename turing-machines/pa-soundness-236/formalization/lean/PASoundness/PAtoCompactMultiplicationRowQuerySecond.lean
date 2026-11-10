import PASoundness.PAtoCompactMultiplicationRowQueryFirst

/-! Capture-safe second queried edge case for the explicit new-row branch.
The row witnesses are alpha-freshened before the queried coordinates are
renamed, so the queried output label 9 is not captured. This does not build a
row graph or establish multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationRowQuerySecond
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFixedFirstCoverageBase PASoundness.PAtoCompactFixedFirstRowWitnessAlpha
open PASoundness.PAtoCompactMultiplicationRowQueryFirst
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The explicit pair descriptions for queried product coordinates 7,8,9. -/
def queryPairsSecond : Formula := namedBoth (pairFormula 63 18 9) (pairFormula 18 7 8)
/-- The queried major coordinate equals the fixed row major, and the minor
and output form an edge of the supplied map. -/
def queryResultSecond : Formula := namedBoth (.equal 7 30)
  (namedBoth (.member 31 8) (graphFormula 6 8 9))

private def F0 : Formula := .imp queryPairs (.imp freshRowWitness queryResult)
private def F1 : Formula := replace 3 7 F0
private def F2 : Formula := replace 4 8 F1
private def F3 : Formula := replace 5 9 F2

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

private def at9 : KDerivation F3.encode := by
  have hi := universalInstance 5 9 F2 (by decide) (by decide) (by decide)
  exact .mp (.generalize 5 at8) hi

private theorem final_shape : F3 = .imp queryPairsSecond (.imp freshRowWitness queryResultSecond) := by decide

/-- For the actual row-witness branch and two descriptions of the same
queried outer edge, obtain the major equality and the queried map edge. -/
def row_query_second : KDerivation (imp queryPairsSecond.encode
    (imp (replace 9 63 rowWitness).encode queryResultSecond.encode)) := by
  have h := at9
  rw [final_shape] at h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(replace 9 63 rowWitness).encode,queryPairsSecond.encode]
  have hr : Context Γ (replace 9 63 rowWitness).encode := .head _ _
  have hq : Context Γ queryPairsSecond.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ freshRowWitness.encode := .mp hr (.closed row_witness_alpha.1)
  exact .mp hf (.mp hq (.closed h))

theorem row_query_second_certificate : theoremCode (certificate row_query_second) =
    imp queryPairsSecond.encode (imp (replace 9 63 rowWitness).encode queryResultSecond.encode) :=
  certificate_correct _
end PASoundness.PAtoCompactMultiplicationRowQuerySecond
#print axioms PASoundness.PAtoCompactMultiplicationRowQuerySecond.row_query_second
#print axioms PASoundness.PAtoCompactMultiplicationRowQuerySecond.row_query_second_certificate
