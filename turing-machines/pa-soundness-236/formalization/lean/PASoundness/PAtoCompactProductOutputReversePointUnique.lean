import PASoundness.PAtoCompactProductOutputPairedReverse
import PASoundness.PAtoCompactProductOutputSourceSameImage

/-! Two retained source/image bodies with a common target have the same
ordered source-product coordinates. Both factor guards and the source matrix
and output bijection remain explicit; no existential paths are eliminated. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputReversePointUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductOutputImagePoint PASoundness.PAtoCompactProductOutputReverseCoverage
open PASoundness.PAtoCompactProductOutputCollectionInsideConditional PASoundness.PAtoCompactProductOutputPairedReverse
open PASoundness.PAtoCompactProductOutputSourceSameImage

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def rivalSource : Formula := replace 32 50 (replace 31 53 (replace 30 51 sourceBody))
def rivalBody : Formula := replace 32 50 (replace 31 53 (replace 30 51 PAtoCompactProductOutputImagePoint.pairedBody))
def rivalUnique : Formula := replace 32 50 (replace 31 53 (replace 30 51 PAtoCompactProductOutputImageUnique.sourceUnique))
def coordinateUnique : Formula := .imp (namedBoth (.member 43 7)
  (namedBoth (.member 44 8) (tripleFormula 7 8 32)))
  (namedBoth (.equal 7 30) (.equal 8 31))
def pointGuard : Formula := namedBoth assumptions (namedBoth (.member 43 30)
  (namedBoth (.member 44 31) (namedBoth (.member 43 51) (.member 44 53))))

theorem rival_body_shape : rivalBody = namedBoth rivalSource rivalImage := by decide
theorem rival_source_shape : rivalSource = namedBoth (.member 0 50)
  (namedBoth (tripleFormula 51 53 50) (.all 9 rivalUnique)) := by decide
theorem selected_source_shape : sourceBody = namedBoth (.member 0 32)
  (namedBoth (tripleFormula 30 31 32) (.all 9 PAtoCompactProductOutputImageUnique.sourceUnique)) := by decide
theorem reverse_shape : relocatedReverse = namedBoth (.member 43 30)
  (namedBoth (.member 44 31) (namedBoth (tripleFormula 30 31 32)
    (.all 7 (.all 8 coordinateUnique)))) := by decide

/-- At a common target output, rival factor coordinates equal selected
coordinates in the stated orientation. -/
def point_unique : KDerivation (imp pointGuard.encode (imp PAtoCompactProductOutputImagePoint.pairedBody.encode
    (imp rivalBody.encode (both (equal 51 30) (equal 53 31))))) := by
  have h7 := universalInstance 7 51 (.all 8 coordinateUnique) (by decide) (by decide) (by decide)
  have hs7 : replace 7 51 (.all 8 coordinateUnique) = .all 8 (replace 7 51 coordinateUnique) := by decide
  rw [hs7] at h7
  have h8 := universalInstance 8 53 (replace 7 51 coordinateUnique) (by decide) (by decide) (by decide)
  have hs8 : replace 8 53 (replace 7 51 coordinateUnique) = .imp
      (namedBoth (.member 43 51) (namedBoth (.member 44 53) (tripleFormula 51 53 32)))
      (namedBoth (.equal 51 30) (.equal 53 31)) := by decide
  rw [hs8] at h8
  have hm := (equalityReplace 50 32 (tripleFormula 51 53 50) (by decide) (by decide)).1
  have hms : replace 50 32 (tripleFormula 51 53 50) = tripleFormula 51 53 32 := by decide
  rw [hms] at hm
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [rivalBody.encode,PAtoCompactProductOutputImagePoint.pairedBody.encode,pointGuard.encode]
  have hr : Context Γ rivalBody.encode := .head _ _
  have hp : Context Γ PAtoCompactProductOutputImagePoint.pairedBody.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ pointGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both assumptions.encode (both (member 43 30) (both (member 44 31)
      (both (member 43 51) (member 44 53))))) := by
    simpa [pointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have ha : Context Γ (both relocatedMatrix.encode PAtoCompactProductMatchFactorImages.firstBijection.encode) := by
    simpa [assumptions, relocatedMatrix, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionLeft hg'
  have hp' : Context Γ (both sourceBody.encode imageBody.encode) := by
    simpa [PAtoCompactProductOutputImagePoint.pairedBody, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using hp
  have hr' : Context Γ (both rivalSource.encode rivalImage.encode) := by
    simpa [rival_body_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hr
  have hps : Context Γ (both (member 0 32) (both (tripleFormula 30 31 32).encode
      (Formula.all 9 PAtoCompactProductOutputImageUnique.sourceUnique).encode)) := by
    simpa [selected_source_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionLeft hp'
  have hrs : Context Γ (both (member 0 50) (both (tripleFormula 51 53 50).encode
      (Formula.all 9 rivalUnique).encode)) := by
    simpa [rival_source_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionLeft hr'
  have heguard : Context Γ sameImageGuard.encode := by
    simpa [sameImageGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionRight ha)
        (Context.conjunctionIntro (Context.conjunctionLeft hps)
          (Context.conjunctionIntro (Context.conjunctionLeft hrs)
            (Context.conjunctionIntro (Context.conjunctionRight hp') (Context.conjunctionRight hr'))))
  have he := Context.mp heguard (.closed source_same_image)
  have hreverse := Context.mp hp (Context.mp (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg')))
    (Context.mp (Context.conjunctionLeft (Context.conjunctionRight hg'))
      (Context.mp (Context.conjunctionLeft hg') (.closed paired_reverse))))
  have hreverse' : Context Γ (both (member 43 30) (both (member 44 31)
      (both (tripleFormula 30 31 32).encode (allCode 7 (allCode 8 coordinateUnique.encode))))) := by
    simpa [reverse_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hreverse
  have ht := Context.mp (Context.conjunctionLeft (Context.conjunctionRight hrs))
    (Context.mp (Context.eqSymm he) (.closed hm))
  have hcomp : Context Γ (namedBoth (.member 43 51)
      (namedBoth (.member 44 53) (tripleFormula 51 53 32))).encode := by
    simpa [namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))))
        (Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))) ht)
  have hu := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hreverse'))
  have hu' := Context.mp (Context.mp hu (.closed h7)) (.closed h8)
  simpa [namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using Context.mp hcomp hu'

theorem point_unique_certificate : theoremCode (certificate point_unique) =
    imp pointGuard.encode (imp PAtoCompactProductOutputImagePoint.pairedBody.encode
      (imp rivalBody.encode (both (equal 51 30) (equal 53 31)))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputReversePointUnique

#print axioms PASoundness.PAtoCompactProductOutputReversePointUnique.point_unique
#print axioms PASoundness.PAtoCompactProductOutputReversePointUnique.point_unique_certificate
