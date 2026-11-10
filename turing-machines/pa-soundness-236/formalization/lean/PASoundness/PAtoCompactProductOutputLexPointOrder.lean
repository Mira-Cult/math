import PASoundness.PAtoCompactProductOutputLexPoints
import PASoundness.PAtoCompactZeroSuccessor

/-! The source product lex comparison and the output isomorphism order
comparison compose to the same lex order on their two target images. Both
point guards remain explicit. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputLexPointOrder

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductOutputReverseCoverage
open PASoundness.PAtoCompactProductMatchFactorOrderPoint PASoundness.PAtoCompactProductOutputLexPoints

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceGuard : Formula := namedBoth (.member 43 30) (namedBoth (.member 44 31)
  (namedBoth (.member 0 32) (namedBoth (.member 43 50) (namedBoth (.member 44 51)
    (namedBoth (.member 0 52) (namedBoth (tripleFormula 30 31 32) (tripleFormula 50 51 52)))))))
def imageGuard : Formula := namedBoth (.member 0 32) (namedBoth (.member 0 52)
  (namedBoth (.member 42 33) (namedBoth (.member 42 55)
    (namedBoth (graphFormula 40 32 33) (graphFormula 40 52 55)))))
def sourceLex : Formula := namedEither (.member 50 30) (namedBoth (.equal 30 50) (.member 51 31))
def sourceComparison : Formula := namedBoth (.imp (.member 52 32) sourceLex)
  (.imp sourceLex (.member 52 32))
def imageComparison : Formula := namedBoth (.imp (.member 52 32) (.member 55 33))
  (.imp (.member 55 33) (.member 52 32))
def targetComparison : Formula := namedBoth (.imp (.member 55 33) sourceLex)
  (.imp sourceLex (.member 55 33))
def pointGuard : Formula := namedBoth relocatedMatrix (namedBoth firstOrder (namedBoth sourceGuard imageGuard))

theorem source_point_shape : sourceLexPoint = .imp sourceGuard sourceComparison := by decide
theorem image_point_shape : imageOrderPoint = .imp imageGuard imageComparison := by decide

/-- The target image ordering agrees with the source factor-pair lex order. -/
def target_lex_point : KDerivation (imp pointGuard.encode targetComparison.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [pointGuard.encode]
  have hg : Context Γ pointGuard.encode := .head _ _
  have hg' : Context Γ (both relocatedMatrix.encode (both firstOrder.encode
      (both sourceGuard.encode imageGuard.encode))) := by
    simpa [pointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hs0 : Context Γ sourceLexPoint.encode :=
    .mp (Context.conjunctionLeft hg') (.closed source_lex_point)
  rw [source_point_shape] at hs0
  have hs : Context Γ sourceComparison.encode :=
    .mp (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg'))) hs0
  have hi0 : Context Γ imageOrderPoint.encode :=
    .mp (Context.conjunctionLeft (Context.conjunctionRight hg')) (.closed image_order_point)
  rw [image_point_shape] at hi0
  have hi : Context Γ imageComparison.encode :=
    .mp (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))) hi0
  have hs' : Context Γ (both (imp (member 52 32) sourceLex.encode) (imp sourceLex.encode (member 52 32))) := by
    simpa [source_point_shape, sourceComparison, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using hs
  have hi' : Context Γ (both (imp (member 52 32) (member 55 33)) (imp (member 55 33) (member 52 32))) := by
    simpa [image_point_shape, imageComparison, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using hi
  have hf : Context Γ (imp (member 55 33) sourceLex.encode) := by
    apply Context.deduction
    let Δ := member 55 33 :: Γ
    have hx : Context Δ (member 55 33) := .head _ _
    have hsrc := Context.mp hx (.under (Context.conjunctionRight hi') _)
    exact .mp hsrc (.under (Context.conjunctionLeft hs') _)
  have hb : Context Γ (imp sourceLex.encode (member 55 33)) := by
    apply Context.deduction
    let Δ := sourceLex.encode :: Γ
    have hx : Context Δ sourceLex.encode := .head _ _
    have hsrc := Context.mp hx (.under (Context.conjunctionRight hs') _)
    exact .mp hsrc (.under (Context.conjunctionLeft hi') _)
  simpa [targetComparison, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
    Context.conjunctionIntro hf hb

theorem target_lex_point_certificate : theoremCode (certificate target_lex_point) =
    imp pointGuard.encode targetComparison.encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputLexPointOrder

#print axioms PASoundness.PAtoCompactProductOutputLexPointOrder.target_lex_point
#print axioms PASoundness.PAtoCompactProductOutputLexPointOrder.target_lex_point_certificate
