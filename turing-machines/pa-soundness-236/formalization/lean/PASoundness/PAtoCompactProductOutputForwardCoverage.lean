import PASoundness.PAtoCompactProductOutputActualPoint
import PASoundness.PAtoCompactProductOutputImageRelation
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Pointwise forward coverage of the actual collected output graph. The
source product matrix, output bijection, actual graph invariant and both
factor memberships remain explicit hypotheses. This is not uniqueness or a
complete target product matrix. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputForwardCoverage

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductOutputImagePoint
open PASoundness.PAtoCompactProductOutputImageRelation PASoundness.PAtoCompactProductOutputActualPoint
open PASoundness.PAtoCompactProductOutputCollectionInsideConditional

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceFrame : Formula := .imp sourceMatrix (.imp firstBijection
  (.imp (.member 80 30) (.imp (.member 81 31) (.ex 33 imagePath))))
def relocatedFrame : Formula := replace 81 44 (replace 80 43 sourceFrame)
def relocatedMatrix : Formula := replace 81 44 (replace 80 43 sourceMatrix)
def pointGuard : Formula := namedBoth actualInvariant (namedBoth (.member 43 30) (.member 44 31))
def forwardResult : Formula := namedBoth (.member 42 33) selectedTriple

theorem relocated_frame_shape : relocatedFrame = .imp relocatedMatrix (.imp firstBijection
    (.imp (.member 43 30) (.imp (.member 44 31) (.ex 33 imagePath)))) := by decide

def relocated_image_exists : KDerivation (imp relocatedMatrix.encode (imp firstBijection.encode
    (imp (member 43 30) (imp (member 44 31) (existsCode 33 imagePath.encode))))) := by
  have h0 : KDerivation sourceFrame.encode := by
    simpa [sourceFrame, CompactNamed.Formula.encode] using image_path_exists
  have h1 := replace_derivation 80 43 sourceFrame (by decide) (by decide) h0
  have h2 := replace_derivation 81 44 (replace 80 43 sourceFrame) (by decide) (by decide) h1
  change KDerivation relocatedFrame.encode at h2
  rw [relocated_frame_shape] at h2
  simpa only [CompactNamed.Formula.encode] using h2

def body_to_forward : KDerivation (imp pointGuard.encode (imp pairedBody.encode forwardResult.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [pairedBody.encode,pointGuard.encode]
  have hb : Context Γ pairedBody.encode := .head _ _
  have hg : Context Γ pointGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both actualInvariant.encode (both (member 43 30) (member 44 31))) := by
    simpa [pointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have h := Context.mp hb (Context.mp (Context.conjunctionRight (Context.conjunctionRight hg'))
    (Context.mp (Context.conjunctionLeft (Context.conjunctionRight hg'))
      (Context.mp (Context.conjunctionLeft hg') (.closed selected_body_in_graph))))
  simpa [forwardResult, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h

/-- Every guarded factor pair has a target member and a triple in the same
supplied actual graph. This is pointwise at factors 30,31. -/
def forward_coverage : KDerivation (imp assumptions.encode (imp actualInvariant.encode
    (imp (member 43 30) (imp (member 44 31) (existsCode 33 forwardResult.encode))))) := by
  have h32 := guarded_exists_left 32 pointGuard.encode pairedBody.encode forwardResult.encode
    (free_vacuity 32 pointGuard (by decide)) (forwardResult.vacuity 32 (by decide)) body_to_forward
  have h33 := conditionalExistsCongr 33 (free_vacuity 33 pointGuard (by decide)) h32
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 44 31,member 43 30,actualInvariant.encode,assumptions.encode]
  have hy : Context Γ (member 44 31) := .head _ _
  have hx : Context Γ (member 43 30) := .hypothesis (by simp [Γ])
  have hi : Context Γ actualInvariant.encode := .hypothesis (by simp [Γ])
  have ha : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have ha' : Context Γ (both relocatedMatrix.encode firstBijection.encode) := by
    simpa [assumptions, relocatedMatrix, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using ha
  have hg : Context Γ pointGuard.encode := by
    simpa [pointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hi (Context.conjunctionIntro hx hy)
  have he := Context.mp hy (Context.mp hx (Context.mp (Context.conjunctionRight ha')
    (Context.mp (Context.conjunctionLeft ha') (.closed relocated_image_exists))))
  have he' : Context Γ (existsCode 33 (existsCode 32 pairedBody.encode)) := by
    simpa [imagePath, CompactNamed.Formula.encode] using he
  exact .mp he' (.mp hg (.closed h33))

theorem forward_coverage_certificate : theoremCode (certificate forward_coverage) =
    imp assumptions.encode (imp actualInvariant.encode (imp (member 43 30)
      (imp (member 44 31) (existsCode 33 forwardResult.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputForwardCoverage

#print axioms PASoundness.PAtoCompactProductOutputForwardCoverage.relocated_image_exists
#print axioms PASoundness.PAtoCompactProductOutputForwardCoverage.body_to_forward
#print axioms PASoundness.PAtoCompactProductOutputForwardCoverage.forward_coverage
#print axioms PASoundness.PAtoCompactProductOutputForwardCoverage.forward_coverage_certificate
