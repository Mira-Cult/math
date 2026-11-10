import PASoundness.PAtoCompactProductOutputSourcePoint
import PASoundness.PAtoCompactProductOutputCollectionInsideConditional

/-! Select the unique source coordinates and an output-bijection image for
the inside-source endpoint of a prefix successor. This is one ingredient of
the inside branch, not the graph-extension invariant. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputInsideSelected

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductOutputSourcePoint
open PASoundness.PAtoCompactProductOutputCollectionInsideConditional
open PASoundness.PAtoCompactProductOutputImagePoint
open PASoundness.PAtoCompactProductMatchFactorImages

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def pointFrame : Formula := .imp sourceGuard (.ex 30 (.ex 31 (.ex 33 selectedBody)))
def relocatedFrame : Formula := replace 32 74 (replace 81 44 (replace 80 43 pointFrame))
def relocatedBody : Formula := replace 32 74 (replace 81 44 (replace 80 43 selectedBody))

theorem relocated_frame_shape : relocatedFrame = .imp
    (namedBoth (replace 81 44 (replace 80 43 sourceMatrix))
      (namedBoth firstBijection (.member 0 74)))
    (.ex 30 (.ex 31 (.ex 33 relocatedBody))) := by decide

/-- The endpoint 74 and its three selected witnesses all refer to the same
source output. The source-product and bijection hypotheses remain literal. -/
def inside_selected_point : KDerivation (imp assumptions.encode (imp (member 0 74)
    (existsCode 30 (existsCode 31 (existsCode 33 relocatedBody.encode))))) := by
  have h0 : KDerivation pointFrame.encode := by
    simpa [pointFrame, CompactNamed.Formula.encode] using selected_source_point
  have h1 := replace_derivation 80 43 pointFrame (by decide) (by decide) h0
  have h2 := replace_derivation 81 44 (replace 80 43 pointFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 32 74 (replace 81 44 (replace 80 43 pointFrame)) (by decide) (by decide) h2
  have hf : KDerivation (imp (namedBoth (replace 81 44 (replace 80 43 sourceMatrix))
      (namedBoth firstBijection (.member 0 74))).encode
      (existsCode 30 (existsCode 31 (existsCode 33 relocatedBody.encode)))) := by
    change KDerivation relocatedFrame.encode at h3
    rw [relocated_frame_shape] at h3
    simpa only [CompactNamed.Formula.encode] using h3
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 74, assumptions.encode]
  have hx : Context Γ (member 0 74) := .head _ _
  have hh : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hh' : Context Γ (both (replace 81 44 (replace 80 43 sourceMatrix)).encode
      firstBijection.encode) := by
    simpa [assumptions, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode,
      both, neg] using hh
  have hg : Context Γ (namedBoth (replace 81 44 (replace 80 43 sourceMatrix))
      (namedBoth firstBijection (.member 0 74))).encode := by
    simpa [namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionLeft hh')
        (Context.conjunctionIntro (Context.conjunctionRight hh') hx)
  exact .mp hg (.closed hf)

theorem inside_selected_point_certificate : theoremCode (certificate inside_selected_point) =
    imp assumptions.encode (imp (member 0 74)
      (existsCode 30 (existsCode 31 (existsCode 33 relocatedBody.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputInsideSelected

#print axioms PASoundness.PAtoCompactProductOutputInsideSelected.inside_selected_point
#print axioms PASoundness.PAtoCompactProductOutputInsideSelected.inside_selected_point_certificate
