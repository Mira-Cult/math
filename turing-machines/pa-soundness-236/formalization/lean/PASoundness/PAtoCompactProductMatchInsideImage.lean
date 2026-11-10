import PASoundness.PAtoCompactProductMatchCollectionInsideConditional
import PASoundness.PAtoCompactProductMatchRelation
import PASoundness.PAtoCompactScopedActiveReplace

/-! Choose the target match for an inside-source successor endpoint. This
constructs the pointwise witness under the four supplied graph matrices; it
does not adjoin an edge, prove the inside extension, or collect a graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchInsideImage

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchRelation PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductMatchCollectionInsideConditional

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceFrame : Formula := .imp productMatrix (.imp (.member 2 32)
  (.imp firstBijection (.imp secondBijection (.imp targetMatrix (.ex 35 path)))))

def selectedPath : Formula := replace 32 74 path

theorem source_replacement : replace 32 74 sourceFrame =
    .imp productMatrix (.imp (.member 2 74)
      (.imp firstBijection (.imp secondBijection (.imp targetMatrix (.ex 35 selectedPath))))) := by decide

/-- For an endpoint 74 belonging to the source output domain, select a
target output and its complete product/factor matching path. -/
def inside_image_exists : KDerivation
    (imp assumptions.encode (imp (member 2 74) (existsCode 35 selectedPath.encode))) := by
  have hsource : KDerivation sourceFrame.encode := by
    simpa [sourceFrame, Formula.encode] using path_exists
  have hi := replace_derivation 32 74 sourceFrame (by decide) (by decide) hsource
  rw [source_replacement] at hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 2 74,assumptions.encode]
  have hx : Context Γ (member 2 74) := .head _ _
  have hh : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hh' : Context Γ (both productMatrix.encode
      (both firstBijection.encode (both secondBijection.encode targetMatrix.encode))) := by
    simpa [assumptions, namedBoth, Formula.not, Formula.encode, both, neg] using hh
  have hp := Context.conjunctionLeft hh'
  have hb₁ := Context.conjunctionLeft (Context.conjunctionRight hh')
  have hb₂ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hh'))
  have ht := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hh'))
  exact .mp ht (.mp hb₂ (.mp hb₁ (.mp hx (.mp hp (.closed hi)))))

theorem inside_image_exists_certificate : theoremCode (certificate inside_image_exists) =
    imp assumptions.encode (imp (member 2 74) (existsCode 35 selectedPath.encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactProductMatchInsideImage

#print axioms PASoundness.PAtoCompactProductMatchInsideImage.inside_image_exists
#print axioms PASoundness.PAtoCompactProductMatchInsideImage.inside_image_exists_certificate
