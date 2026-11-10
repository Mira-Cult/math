import PASoundness.PAtoCompactProductOutputLexBodyOrder
import PASoundness.PAtoCompactProductOutputImageRelation
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Lift the guarded pointwise lex comparison through two image paths while
retaining their actual source-output witnesses. Graph-wide order remains a
separate step. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputLexPathOrder

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactProductOutputImagePoint PASoundness.PAtoCompactProductOutputImageRelation
open PASoundness.PAtoCompactProductOutputLexPointOrder PASoundness.PAtoCompactProductOutputLexBodyOrder

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def otherInput : Formula := replace 33 55 (replace 31 51 (replace 30 50 imagePath))
def otherPath : Formula := .ex 52 otherPair
def firstGuard : Formula := namedBoth guard pairedBody
def secondGuard : Formula := namedBoth guard otherPath

theorem other_input_shape : otherInput = .ex 32
    (replace 33 55 (replace 31 51 (replace 30 50 pairedBody))) := by decide
theorem other_body_shape : replace 32 52 (replace 33 55 (replace 31 51
    (replace 30 50 pairedBody))) = otherPair := by decide

def other_alpha : KDerivation (imp otherInput.encode otherPath.encode) := by
  have h := (existentialAlpha 32 52 (replace 33 55 (replace 31 51 (replace 30 50 pairedBody)))
    (by decide) (by decide) (by decide)).1
  rw [other_body_shape] at h
  simpa [other_input_shape, otherPath, CompactNamed.Formula.encode] using h

def pair_point : KDerivation (imp firstGuard.encode (imp otherPair.encode targetComparison.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [otherPair.encode,firstGuard.encode]
  have ho : Context Γ otherPair.encode := .head _ _
  have hg : Context Γ firstGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both guard.encode pairedBody.encode) := by
    simpa [firstGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  exact .mp ho (.mp (Context.conjunctionRight hg') (.mp (Context.conjunctionLeft hg') (.closed body_order)))

def eliminate_other : KDerivation (imp firstGuard.encode (imp otherPath.encode targetComparison.encode)) := by
  have h := guarded_exists_left 52 firstGuard.encode otherPair.encode targetComparison.encode
    (free_vacuity 52 firstGuard (by decide)) (targetComparison.vacuity 52 (by decide)) pair_point
  simpa [otherPath, CompactNamed.Formula.encode] using h

def selected_point : KDerivation (imp secondGuard.encode (imp pairedBody.encode targetComparison.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [pairedBody.encode,secondGuard.encode]
  have hp : Context Γ pairedBody.encode := .head _ _
  have hg : Context Γ secondGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both guard.encode otherPath.encode) := by
    simpa [secondGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hf : Context Γ firstGuard.encode := by
    simpa [firstGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionLeft hg') hp
  exact .mp (Context.conjunctionRight hg') (.mp hf (.closed eliminate_other))

/-- The two paths imply the target-order/lex comparison under the explicit
source matrix, output order and factor memberships. -/
def path_order : KDerivation (imp guard.encode (imp imagePath.encode
    (imp otherInput.encode targetComparison.encode))) := by
  have h32 := guarded_exists_left 32 secondGuard.encode pairedBody.encode targetComparison.encode
    (free_vacuity 32 secondGuard (by decide)) (targetComparison.vacuity 32 (by decide)) selected_point
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [otherInput.encode,imagePath.encode,guard.encode]
  have ho : Context Γ otherInput.encode := .head _ _
  have hp : Context Γ imagePath.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ guard.encode := .hypothesis (by simp [Γ])
  have ho' : Context Γ otherPath.encode := .mp ho (.closed other_alpha)
  have hs : Context Γ secondGuard.encode := by
    simpa [secondGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hg ho'
  have hp' : Context Γ (existsCode 32 pairedBody.encode) := by
    simpa [imagePath, CompactNamed.Formula.encode] using hp
  exact .mp hp' (.mp hs (.closed h32))

theorem path_order_certificate : theoremCode (certificate path_order) =
    imp guard.encode (imp imagePath.encode (imp otherInput.encode targetComparison.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputLexPathOrder

#print axioms PASoundness.PAtoCompactProductOutputLexPathOrder.path_order
#print axioms PASoundness.PAtoCompactProductOutputLexPathOrder.path_order_certificate
