import PASoundness.PAtoCompactCommonSourceSpanMatrix
import PASoundness.PAtoCompactPartialInverseCandidateProjection
import PASoundness.PAtoCompactPartialInverseInductionFixture
import PASoundness.PAtoCompactCandidateFieldTransport

/-! Construct a restricted inverse graph for the first common-source input.
The first bijection and common-source candidate remain explicit object-level
antecedents. Graph/source moves are capture-safe; neither image object is
assumed candidate. This module does not yet eliminate the inverse witness or
prove the target isomorphism. -/
namespace PASoundness.PAtoCompactCommonSourceSpanInverseWitness

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactRestrictedInverseFirst PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactCandidateFieldTransport
open PASoundness.PAtoCompactCommonSourceSpanInputMatrices PASoundness.PAtoCompactCommonSourceSpanInverseRestriction

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def firstBijection14 : Formula := replace 6 14 firstBijection

private def sourceFrame : Formula := .imp bijectionFormula (.imp (namedCandidate 0)
  (.ex 7 restrictedInverseMatrix))
private def movedGraph : Formula := replace 6 14 sourceFrame
private def movedSource : Formula := replace 0 25 movedGraph
private def movedTarget : Formula := replace 1 0 movedSource
private def swapped : Formula := replace 25 1 movedTarget
private def inverseBody7 : Formula := replace 25 1 (replace 1 0
  (replace 0 25 (replace 6 14 restrictedInverseMatrix)))

private theorem source_frame_code : sourceFrame.encode =
    imp bijectionFormula.encode (imp (namedCandidate 0).encode
      (existsCode 7 restrictedInverseMatrix.encode)) := rfl

private theorem swapped_alignment : swapped =
    .imp firstBijection14 (.imp (namedCandidate 1) (.ex 7 inverseBody7)) := by decide

private theorem inverse_body_alignment : replace 7 6 inverseBody7 = renamedRestriction := by rfl

/-- For a common candidate source, K constructs a graph at 6 representing the
restricted inverse of the actual first bijection on graph 14. -/
def restricted_inverse_exists : KDerivation
    (imp firstBijection14.encode (imp (namedCandidate 1).encode
      (existsCode 6 renamedRestriction.encode))) := by
  have hbase : KDerivation sourceFrame.encode := by
    rw [source_frame_code]
    have hcandidate : KDerivation (imp (namedCandidate 0).encode
        (PASoundness.PAtoCompactPartialInverseAtSource.namedCandidate 0).encode) := by
      simpa only [PASoundness.PAtoCompactPartialCompositionAtSource.named_candidate_code,
        PASoundness.PAtoCompactPartialInverseAtSource.named_candidate_code] using
          witness_field 0 37 32 33 34 30 35 13 36 10 (by decide) (by decide)
    have hinverse := PASoundness.PAtoCompactPartialInverseCandidateProjection.candidate_source_inverse
      PASoundness.PAtoCompactPartialInverseInductionFixture.fixed_induction
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(namedCandidate 0).encode,bijectionFormula.encode]
    have hc : Context Γ (namedCandidate 0).encode := .head _ _
    have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
    have hc' : Context Γ (PASoundness.PAtoCompactPartialInverseAtSource.namedCandidate 0).encode :=
      .mp hc (.closed hcandidate)
    exact .mp hc' (.mp hb (.closed hinverse))
  have h0 := replace_derivation 6 14 sourceFrame (by decide) (by decide) hbase
  have h1 := replace_derivation 0 25 movedGraph (by decide) (by decide) (by simpa only [movedGraph] using h0)
  have h2 := replace_derivation 1 0 movedSource (by decide) (by decide) (by simpa only [movedSource] using h1)
  have h3 := replace_derivation 25 1 movedTarget (by decide) (by decide) (by simpa only [movedTarget] using h2)
  have hs : KDerivation swapped.encode := by simpa only [swapped] using h3
  rw [swapped_alignment] at hs
  have ha := (existentialAlpha 7 6 inverseBody7 (by decide) (by decide) (by decide)).1
  rw [inverse_body_alignment] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(namedCandidate 1).encode,firstBijection14.encode]
  have hc : Context Γ (namedCandidate 1).encode := .head _ _
  have hf : Context Γ firstBijection14.encode := .hypothesis (by simp [Γ])
  have hi : Context Γ (existsCode 7 inverseBody7.encode) := .mp hc (.mp hf (.closed hs))
  exact .mp hi (.closed ha)

theorem restricted_inverse_exists_certificate :
    theoremCode (certificate restricted_inverse_exists) =
      imp firstBijection14.encode (imp (namedCandidate 1).encode
        (existsCode 6 renamedRestriction.encode)) := certificate_correct restricted_inverse_exists

end PASoundness.PAtoCompactCommonSourceSpanInverseWitness

#print axioms PASoundness.PAtoCompactCommonSourceSpanInverseWitness.firstBijection14
#print axioms PASoundness.PAtoCompactCommonSourceSpanInverseWitness.restricted_inverse_exists
#print axioms PASoundness.PAtoCompactCommonSourceSpanInverseWitness.restricted_inverse_exists_certificate
