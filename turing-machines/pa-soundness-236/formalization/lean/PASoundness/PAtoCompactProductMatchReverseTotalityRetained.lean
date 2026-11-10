import PASoundness.PAtoCompactProductMatchReverseTotality
import PASoundness.PAtoCompactProductMatchReverseAtCoordinatesRetained

/-! Reverse target coverage with source output membership retained inside
the same existential source and coordinate witnesses. This does not itself
assert that the match is an edge of a represented graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReverseTotalityRetained

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactExistsCommute PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchTargetOutput PASoundness.PAtoCompactProductMatchReverseProduct
open PASoundness.PAtoCompactProductMatchReverseReconstruct PASoundness.PAtoCompactProductMatchReverseAtCoordinates
open PASoundness.PAtoCompactProductMatchReverseAtCoordinatesRetained
open PASoundness.PAtoCompactProductMatchReverseRetainedSource

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def reverse_total_retaining_source : KDerivation (imp productMatrix.encode (imp firstBijection.encode
    (imp secondBijection.encode (imp targetMatrix.encode (imp (member 44 55)
      (existsCode 32 (existsCode 30 (existsCode 31 (existsCode 33 (existsCode 34 retainedSourceBody.encode)))))))))) := by
  have h34 := conditionalExistsCongr 34 (sourceGuard.vacuity 34 (by decide)) path_at_coordinates_retaining_source
  have h33 := conditionalExistsCongr 33 (sourceGuard.vacuity 33 (by decide)) h34
  let B := retainedSourceBody.encode
  have h1 := existsCongr 33 (existsCongr 34 (existsCongr 30 (exists_commute 31 32 B)))
  have h2 := existsCongr 33 (existsCongr 34 (exists_commute 30 32 (existsCode 31 B)))
  have h3 := existsCongr 33 (exists_commute 34 32 (existsCode 30 (existsCode 31 B)))
  have h4 := exists_commute 33 32 (existsCode 34 (existsCode 30 (existsCode 31 B)))
  have h5 := existsCongr 32 (existsCongr 33 (exists_commute 34 30 (existsCode 31 B)))
  have h6 := existsCongr 32 (exists_commute 33 30 (existsCode 34 (existsCode 31 B)))
  have h7 := existsCongr 32 (existsCongr 30 (existsCongr 33 (exists_commute 34 31 B)))
  have h8 := existsCongr 32 (existsCongr 30 (exists_commute 33 31 (existsCode 34 B)))
  have hswap := compose h1 (compose h2 (compose h3 (compose h4
    (compose h5 (compose h6 (compose h7 h8))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 44 55,targetMatrix.encode,secondBijection.encode,firstBijection.encode,productMatrix.encode]
  have hy : Context Γ (member 44 55) := .head _ _
  have ht : Context Γ targetMatrix.encode := .hypothesis (by simp [Γ])
  have hb₂ : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hb₁ : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ productMatrix.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ sourceGuard.encode := by
    have h := Context.conjunctionIntro hp (Context.conjunctionIntro hb₁
      (Context.conjunctionIntro hb₂ (Context.conjunctionIntro ht hy)))
    simpa [sourceGuard, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hc : Context Γ (existsCode 33 (existsCode 34 targetReverseBody.encode)) :=
    .mp hy (.mp ht (.closed target_coordinates))
  have hw := Context.mp hc (Context.mp hg (.closed h33))
  have hout := Context.mp hw (.closed hswap)
  simpa [Γ, B, Formula.encode] using hout


theorem reverse_total_retaining_source_certificate :
    theoremCode (certificate reverse_total_retaining_source) =
      imp productMatrix.encode (imp firstBijection.encode
        (imp secondBijection.encode (imp targetMatrix.encode (imp (member 44 55)
          (existsCode 32 (existsCode 30 (existsCode 31 (existsCode 33 (existsCode 34 retainedSourceBody.encode))))))))) :=
  certificate_correct _

end PASoundness.PAtoCompactProductMatchReverseTotalityRetained

#print axioms PASoundness.PAtoCompactProductMatchReverseTotalityRetained.reverse_total_retaining_source
#print axioms PASoundness.PAtoCompactProductMatchReverseTotalityRetained.reverse_total_retaining_source_certificate
