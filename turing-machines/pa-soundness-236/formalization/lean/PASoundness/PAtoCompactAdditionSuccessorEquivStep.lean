import PASoundness.PAtoCompactAdditionSuccessorIsoMatrix
import PASoundness.PAtoCompactAdditionSuccessorEquivIntro
import PASoundness.PAtoCompactAdditionJointWitness

/-! Local K implication from explicit old hypotheses and supplied extension
witnesses to the canonical equivalence between the source successor and the
new suffix. This module does not assert witness existence, addition totality,
or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorEquivStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactAdditionOldTargetFromBijection
open PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdditionRightContext
open PASoundness.PAtoCompactAdditionSuccessorIsoMatrix
open PASoundness.PAtoCompactAdditionSuccessorEquivIntro
open PASoundness.PAtoCompactAdditionJointWitness
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Source/result transitivity, old filter, old clean matrix and source
successor, with no new pair, graph, or suffix witness included. -/
def fixedHypotheses : Formula := namedBoth suffixF (namedBoth oldMatrixAt
  (namedBoth oldClean (namedBoth sourceS
    (namedBoth (.all 37 (.all 38 (transitiveBody 31 37 38)))
      (.all 37 (.all 38 (transitiveBody 32 37 38)))))))

def suffixWitness : Formula := namedBoth (namedAdjoin 34 32 40 41)
  (.all 35 (namedFilterBody 45 40 35 (Formula.member 33 35).not))

theorem suffix_witness_code : suffixWitness.encode = suffixBody := by rfl

theorem matrix_identity : newMatrixAt = matrixNamed := by decide

/-- For any supplied extension witnesses, the actual canonical equivalence
follows in K. Both transitivity hypotheses concern the source and whole result. -/
def local_equiv : KDerivation (imp fixedHypotheses.encode
    (imp suffixWitness.encode (imp pairF.encode
      (imp graphA.encode (equivAt 38 40).encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [graphA.encode,pairF.encode,suffixWitness.encode,fixedHypotheses.encode]
  have hg : Context Γ graphA.encode := .head _ _
  have hp : Context Γ pairF.encode := .hypothesis (by simp [Γ])
  have hw : Context Γ suffixWitness.encode := .hypothesis (by simp [Γ])
  have hh : Context Γ fixedHypotheses.encode := .hypothesis (by simp [Γ])
  have hf := Context.conjunctionLeft hh
  have hrest := Context.conjunctionRight hh
  have hm := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hc := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hs := Context.conjunctionLeft hrest
  have ht := Context.conjunctionRight hrest
  have hsource := Context.conjunctionLeft ht
  have htarget := Context.conjunctionRight ht
  have hq : Context Γ premises.encode := by
    change Context Γ (both suffixF.encode (both oldMatrixAt.encode
      (both oldClean.encode (both sourceS.encode (both graphA.encode pairF.encode)))))
    exact Context.conjunctionIntro hf (Context.conjunctionIntro hm
      (Context.conjunctionIntro hc (Context.conjunctionIntro hs (Context.conjunctionIntro hg hp))))
  have hd : Context Γ (adjoinCode 34 32 40 41) := by
    exact Context.conjunctionLeft hw
  have hsource' : Context Γ (transitiveCode 31 37 38) := by
    exact hsource
  have htarget' : Context Γ (transitiveCode 32 37 38) := by
    exact htarget
  have hmatrix : Context Γ newMatrixAt.encode :=
    .mp htarget' (.mp hsource' (.mp hd (.mp hq (.closed isomorphism_matrix))))
  rw [matrix_identity] at hmatrix
  exact .mp hmatrix (.closed matrix_to_equiv)

theorem local_equiv_certificate : theoremCode (certificate local_equiv) =
    imp fixedHypotheses.encode (imp suffixWitness.encode (imp pairF.encode
      (imp graphA.encode (equivAt 38 40).encode))) := certificate_correct local_equiv
end PASoundness.PAtoCompactAdditionSuccessorEquivStep
#print axioms PASoundness.PAtoCompactAdditionSuccessorEquivStep.local_equiv
#print axioms PASoundness.PAtoCompactAdditionSuccessorEquivStep.local_equiv_certificate
