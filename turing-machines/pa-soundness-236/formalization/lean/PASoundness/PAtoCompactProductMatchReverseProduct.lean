import PASoundness.PAtoCompactProductMatchTargetOutput
import PASoundness.PAtoCompactMulTermTransportWitness

/-! Reverse-product witness for a target output. This constructs the target
factor coordinates of a supplied target output, retaining the literal
product reverse-uniqueness clause. It does not yet select the factor
preimages or prove reverse matching. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReverseProduct

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactMulTermTransportWitness PASoundness.PAtoCompactProductMatchPointWitness
open PASoundness.PAtoCompactProductMatchTargetOutput

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def baseBody : Formula := replace 31 34 (replace 30 33 selectedReverseBody)

def baseFrame : Formula := .imp productMatrix (.imp (.member 2 32) (.ex 33 (.ex 34 baseBody)))

private def base_coordinates : KDerivation baseFrame.encode := by
  have ha := two_exists_alpha selectedReverseBody 30 31 33 34
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 2 32,productMatrix.encode]
  have hx : Context Γ (member 2 32) := .head _ _
  have hm : Context Γ productMatrix.encode := .hypothesis (by simp [Γ])
  have hw : Context Γ (existsCode 30 (existsCode 31 selectedReverseBody.encode)) :=
    .mp hx (.mp hm (.closed reverse_coordinates))
  simpa [baseFrame, baseBody, Formula.encode] using Context.mp hw (.closed ha.forward)

def targetReverseBody : Formula := replace 32 55 (replace 0 42 (replace 1 43
  (replace 2 44 (replace 6 45 baseBody))))

def targetFrame : Formula := replace 32 55 (replace 0 42 (replace 1 43
  (replace 2 44 (replace 6 45 baseFrame))))

theorem target_frame_shape : targetFrame = .imp targetMatrix (.imp (.member 44 55)
    (.ex 33 (.ex 34 targetReverseBody))) := by decide

/-- An arbitrary member 55 of target product 44 has target coordinates
33,34 with the complete selected reverse-product uniqueness clause. -/
def target_coordinates : KDerivation (imp targetMatrix.encode (imp (member 44 55)
    (existsCode 33 (existsCode 34 targetReverseBody.encode)))) := by
  have h1 := replace_derivation 6 45 baseFrame (by decide) (by decide) base_coordinates
  have h2 := replace_derivation 2 44 (replace 6 45 baseFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 1 43 (replace 2 44 (replace 6 45 baseFrame))
    (by decide) (by decide) h2
  have h4 := replace_derivation 0 42 (replace 1 43 (replace 2 44 (replace 6 45 baseFrame)))
    (by decide) (by decide) h3
  have h5 := replace_derivation 32 55
    (replace 0 42 (replace 1 43 (replace 2 44 (replace 6 45 baseFrame))))
    (by decide) (by decide) h4
  change KDerivation targetFrame.encode at h5
  rw [target_frame_shape] at h5
  simpa [Formula.encode] using h5

theorem target_coordinates_certificate : theoremCode (certificate target_coordinates) =
    imp targetMatrix.encode (imp (member 44 55)
      (existsCode 33 (existsCode 34 targetReverseBody.encode))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchReverseProduct

#print axioms PASoundness.PAtoCompactProductMatchReverseProduct.target_coordinates
#print axioms PASoundness.PAtoCompactProductMatchReverseProduct.target_coordinates_certificate
