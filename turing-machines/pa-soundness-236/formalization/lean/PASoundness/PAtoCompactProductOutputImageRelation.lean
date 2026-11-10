import PASoundness.PAtoCompactProductOutputImageUnique
import PASoundness.PAtoCompactExistsCommute
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! The concrete source-product/output-image relation is total and
functional pointwise on a supplied factor pair. No transported graph has yet
been collected. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputImageRelation

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductOutputImagePoint
open PASoundness.PAtoCompactProductOutputImageUnique PASoundness.PAtoCompactExistsCommute
open PASoundness.PAtoCompactSuccGraphOutputLift

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def imagePath : Formula := .ex 32 pairedBody
def rivalInput : Formula := replace 33 51 imagePath
def rivalPath : Formula := .ex 50 rivalPair

theorem rival_input_shape : rivalInput = .ex 32 (replace 33 51 pairedBody) := by decide
theorem rival_body_shape : replace 32 50 (replace 33 51 pairedBody) = rivalPair := by decide

def rival_alpha : KDerivation (imp rivalInput.encode rivalPath.encode) := by
  have h := (existentialAlpha 32 50 (replace 33 51 pairedBody)
    (by decide) (by decide) (by decide)).1
  rw [rival_body_shape] at h
  simpa [rival_input_shape, rivalPath, Formula.encode] using h

/-- Every displayed factor pair has a target-image path under the source
product matrix and output-isomorphism bijection. -/
def image_path_exists : KDerivation (imp sourceMatrix.encode (imp firstBijection.encode
    (imp (member 80 30) (imp (member 81 31) (existsCode 33 imagePath.encode))))) := by
  have hswap := exists_commute 32 33 pairedBody.encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 81 31,member 80 30,firstBijection.encode,sourceMatrix.encode]
  have hy : Context Γ (member 81 31) := .head _ _
  have hx : Context Γ (member 80 30) := .hypothesis (by simp [Γ])
  have hb : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ sourceMatrix.encode := .hypothesis (by simp [Γ])
  have h := Context.mp hy (Context.mp hx (Context.mp hb (Context.mp hm (.closed paired_output_exists))))
  simpa [Γ, imagePath, Formula.encode] using Context.mp h (.closed hswap)

/-- For the same displayed factor pair, two target-image paths have equal
target outputs; no graph matrix is assumed by this pointwise implication. -/
def image_path_unique : KDerivation (imp imagePath.encode
    (imp rivalInput.encode (equal 51 33))) := by
  let E : Formula := .equal 51 33
  have h50 := guarded_exists_left 50 pairedBody.encode rivalPair.encode E.encode
    (pairedBody.vacuity 50 (by decide)) (E.vacuity 50 (by decide)) paired_image_unique
  have hpoint : KDerivation (imp rivalPath.encode (imp pairedBody.encode E.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [pairedBody.encode,rivalPath.encode]
    have hp : Context Γ pairedBody.encode := .head _ _
    have hr : Context Γ rivalPath.encode := .hypothesis (by simp [Γ])
    simpa [Γ, rivalPath, E, Formula.encode] using Context.mp hr (Context.mp hp (.closed h50))
  have h32 := guarded_exists_left 32 rivalPath.encode pairedBody.encode E.encode
    (rivalPath.vacuity 32 (by decide)) (E.vacuity 32 (by decide)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [rivalInput.encode,imagePath.encode]
  have hr : Context Γ rivalInput.encode := .head _ _
  have hp : Context Γ imagePath.encode := .hypothesis (by simp [Γ])
  have hr' := Context.mp hr (.closed rival_alpha)
  simpa [Γ, imagePath, E, Formula.encode] using Context.mp hp (Context.mp hr' (.closed h32))

theorem image_path_exists_certificate : theoremCode (certificate image_path_exists) =
    imp sourceMatrix.encode (imp firstBijection.encode (imp (member 80 30)
      (imp (member 81 31) (existsCode 33 imagePath.encode)))) := certificate_correct _
theorem image_path_unique_certificate : theoremCode (certificate image_path_unique) =
    imp imagePath.encode (imp rivalInput.encode (equal 51 33)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputImageRelation

#print axioms PASoundness.PAtoCompactProductOutputImageRelation.rival_alpha
#print axioms PASoundness.PAtoCompactProductOutputImageRelation.image_path_exists
#print axioms PASoundness.PAtoCompactProductOutputImageRelation.image_path_unique
#print axioms PASoundness.PAtoCompactProductOutputImageRelation.image_path_exists_certificate
#print axioms PASoundness.PAtoCompactProductOutputImageRelation.image_path_unique_certificate
