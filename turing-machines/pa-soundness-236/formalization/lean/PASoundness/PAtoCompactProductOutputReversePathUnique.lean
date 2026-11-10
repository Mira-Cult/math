import PASoundness.PAtoCompactProductOutputReversePointUnique
import PASoundness.PAtoCompactProductOutputImageRelation
import PASoundness.PAtoCompactSuccGraphOutputLift
import PASoundness.PAtoCompactFreeVacuity

/-! Lift same-target reverse coordinate uniqueness through two actual image
paths, retaining their factor guards and allowing distinct source witnesses. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputReversePathUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactProductOutputImagePoint PASoundness.PAtoCompactProductOutputImageRelation
open PASoundness.PAtoCompactProductOutputReversePointUnique

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def rivalInput : Formula := replace 31 53 (replace 30 51 imagePath)
def rivalPath : Formula := .ex 50 rivalBody
def firstGuard : Formula := namedBoth pointGuard PAtoCompactProductOutputImagePoint.pairedBody
def secondGuard : Formula := namedBoth pointGuard rivalPath
def equalities : Formula := namedBoth (.equal 51 30) (.equal 53 31)

theorem rival_input_shape : rivalInput = .ex 32
    (replace 31 53 (replace 30 51 PAtoCompactProductOutputImagePoint.pairedBody)) := by decide
theorem rival_body_shape : replace 32 50 (replace 31 53 (replace 30 51
    PAtoCompactProductOutputImagePoint.pairedBody)) = rivalBody := by decide

def rival_alpha : KDerivation (imp rivalInput.encode rivalPath.encode) := by
  have h := (existentialAlpha 32 50 (replace 31 53 (replace 30 51
    PAtoCompactProductOutputImagePoint.pairedBody)) (by decide) (by decide) (by decide)).1
  rw [rival_body_shape] at h
  simpa [rival_input_shape, rivalPath, CompactNamed.Formula.encode] using h

def pair_point : KDerivation (imp firstGuard.encode (imp rivalBody.encode equalities.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [rivalBody.encode,firstGuard.encode]
  have hr : Context Γ rivalBody.encode := .head _ _
  have hg : Context Γ firstGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both pointGuard.encode PAtoCompactProductOutputImagePoint.pairedBody.encode) := by
    simpa [firstGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have h := Context.mp hr (Context.mp (Context.conjunctionRight hg')
    (Context.mp (Context.conjunctionLeft hg') (.closed point_unique)))
  simpa [equalities, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h

def eliminate_rival : KDerivation (imp firstGuard.encode (imp rivalPath.encode equalities.encode)) := by
  have h := guarded_exists_left 50 firstGuard.encode rivalBody.encode equalities.encode
    (free_vacuity 50 firstGuard (by decide)) (equalities.vacuity 50 (by decide)) pair_point
  simpa [rivalPath, CompactNamed.Formula.encode] using h

def selected_point : KDerivation (imp secondGuard.encode
    (imp PAtoCompactProductOutputImagePoint.pairedBody.encode equalities.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [PAtoCompactProductOutputImagePoint.pairedBody.encode,secondGuard.encode]
  have hp : Context Γ PAtoCompactProductOutputImagePoint.pairedBody.encode := .head _ _
  have hg : Context Γ secondGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both pointGuard.encode rivalPath.encode) := by
    simpa [secondGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hf : Context Γ firstGuard.encode := by
    simpa [firstGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionLeft hg') hp
  exact .mp (Context.conjunctionRight hg') (.mp hf (.closed eliminate_rival))

/-- Two actual image paths at the same target have identical ordered factor
coordinates, under the supplied matrices and four factor memberships. -/
def path_unique : KDerivation (imp pointGuard.encode
    (imp imagePath.encode (imp rivalInput.encode equalities.encode))) := by
  have h32 := guarded_exists_left 32 secondGuard.encode PAtoCompactProductOutputImagePoint.pairedBody.encode equalities.encode
    (free_vacuity 32 secondGuard (by decide)) (equalities.vacuity 32 (by decide)) selected_point
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [rivalInput.encode,imagePath.encode,pointGuard.encode]
  have hr : Context Γ rivalInput.encode := .head _ _
  have hp : Context Γ imagePath.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ pointGuard.encode := .hypothesis (by simp [Γ])
  have hr' : Context Γ rivalPath.encode := .mp hr (.closed rival_alpha)
  have hs : Context Γ secondGuard.encode := by
    simpa [secondGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hg hr'
  have hp' : Context Γ (existsCode 32 PAtoCompactProductOutputImagePoint.pairedBody.encode) := by
    simpa [imagePath, CompactNamed.Formula.encode] using hp
  exact .mp hp' (.mp hs (.closed h32))

theorem path_unique_certificate : theoremCode (certificate path_unique) =
    imp pointGuard.encode (imp imagePath.encode (imp rivalInput.encode equalities.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputReversePathUnique

#print axioms PASoundness.PAtoCompactProductOutputReversePathUnique.rival_alpha
#print axioms PASoundness.PAtoCompactProductOutputReversePathUnique.pair_point
#print axioms PASoundness.PAtoCompactProductOutputReversePathUnique.eliminate_rival
#print axioms PASoundness.PAtoCompactProductOutputReversePathUnique.selected_point
#print axioms PASoundness.PAtoCompactProductOutputReversePathUnique.path_unique
#print axioms PASoundness.PAtoCompactProductOutputReversePathUnique.path_unique_certificate
