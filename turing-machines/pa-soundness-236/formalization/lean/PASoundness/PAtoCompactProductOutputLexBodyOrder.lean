import PASoundness.PAtoCompactProductOutputLexPointOrder
import PASoundness.PAtoCompactProductOutputImageUnique

/-! Reconstruct the two order point guards from two retained source/image
bodies and four explicit factor memberships. This is pointwise comparison,
not yet graph-wide order or existential path elimination. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputLexBodyOrder

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductOutputReverseCoverage
open PASoundness.PAtoCompactProductMatchFactorOrderPoint PASoundness.PAtoCompactProductOutputImagePoint
open PASoundness.PAtoCompactProductOutputLexPointOrder

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def otherSource : Formula := replace 32 52 (replace 31 51 (replace 30 50 sourceBody))
def otherImage : Formula := replace 33 55 (replace 32 52 imageBody)
def otherPair : Formula := namedBoth otherSource otherImage
def otherUnique : Formula := replace 32 52 (replace 31 51 (replace 30 50
  PAtoCompactProductOutputImageUnique.sourceUnique))
def guard : Formula := namedBoth relocatedMatrix (namedBoth firstOrder
  (namedBoth (.member 43 30) (namedBoth (.member 44 31)
    (namedBoth (.member 43 50) (.member 44 51)))))

theorem other_source_shape : otherSource = namedBoth (.member 0 52)
  (namedBoth (tripleFormula 50 51 52) (.all 9 otherUnique)) := by decide
theorem first_image_shape : imageBody = namedBoth (.member 42 33)
  (namedBoth (graphFormula 40 32 33) (.all 4 (.imp
    (namedBoth (.member 42 4) (graphFormula 40 32 4)) (.equal 4 33)))) := by decide
theorem other_image_shape : otherImage = namedBoth (.member 42 55)
  (namedBoth (graphFormula 40 52 55) (.all 4 (.imp
    (namedBoth (.member 42 4) (graphFormula 40 52 4)) (.equal 4 55)))) := by decide

def body_order : KDerivation (imp guard.encode
    (imp pairedBody.encode (imp otherPair.encode targetComparison.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [otherPair.encode,pairedBody.encode,guard.encode]
  have ho : Context Γ otherPair.encode := .head _ _
  have hp : Context Γ pairedBody.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ guard.encode := .hypothesis (by simp [Γ])
  have ho' : Context Γ (both otherSource.encode otherImage.encode) := by
    simpa [otherPair, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using ho
  have hp' : Context Γ (both sourceBody.encode imageBody.encode) := by
    simpa [pairedBody, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hp
  have hg' : Context Γ (both relocatedMatrix.encode (both firstOrder.encode (both (member 43 30)
      (both (member 44 31) (both (member 43 50) (member 44 51)))))) := by
    simpa [guard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hs : Context Γ (both (member 0 32) (both (tripleFormula 30 31 32).encode
      (Formula.all 9 PAtoCompactProductOutputImageUnique.sourceUnique).encode)) := by
    simpa [PAtoCompactProductOutputImageUnique.source_shape, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using Context.conjunctionLeft hp'
  have ht : Context Γ (both (member 0 52) (both (tripleFormula 50 51 52).encode (Formula.all 9 otherUnique).encode)) := by
    simpa [other_source_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionLeft ho'
  have ha : Context Γ (both (member 42 33) (both (graphFormula 40 32 33).encode
      (Formula.all 4 (.imp (namedBoth (.member 42 4) (graphFormula 40 32 4)) (.equal 4 33))).encode)) := by
    simpa [first_image_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionRight hp'
  have hb : Context Γ (both (member 42 55) (both (graphFormula 40 52 55).encode
      (Formula.all 4 (.imp (namedBoth (.member 42 4) (graphFormula 40 52 4)) (.equal 4 55))).encode)) := by
    simpa [other_image_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionRight ho'
  have hsGuard : Context Γ sourceGuard.encode := by
    simpa [sourceGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg')))
        (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))))
          (Context.conjunctionIntro (Context.conjunctionLeft hs)
            (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))))
              (Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))))
                (Context.conjunctionIntro (Context.conjunctionLeft ht)
                  (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hs)) (Context.conjunctionLeft (Context.conjunctionRight ht))))))))
  have hiGuard : Context Γ imageGuard.encode := by
    simpa [imageGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionLeft hs) (Context.conjunctionIntro (Context.conjunctionLeft ht)
        (Context.conjunctionIntro (Context.conjunctionLeft ha) (Context.conjunctionIntro (Context.conjunctionLeft hb)
          (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight ha))
            (Context.conjunctionLeft (Context.conjunctionRight hb))))))
  have hpoint : Context Γ pointGuard.encode := by
    simpa [pointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionLeft hg') (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hg'))
        (Context.conjunctionIntro hsGuard hiGuard))
  exact .mp hpoint (.closed target_lex_point)

theorem body_order_certificate : theoremCode (certificate body_order) =
    imp guard.encode (imp pairedBody.encode (imp otherPair.encode targetComparison.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputLexBodyOrder

#print axioms PASoundness.PAtoCompactProductOutputLexBodyOrder.body_order
#print axioms PASoundness.PAtoCompactProductOutputLexBodyOrder.body_order_certificate
