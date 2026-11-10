import PASoundness.PAtoCompactProductMatchFactorOrderPoint
import PASoundness.PAtoCompactProductMatchProductLexPoint
import PASoundness.PAtoCompactProductMatchFactorEquality
import PASoundness.PAtoCompactProductIsoPointwiseLex

/-! Literal pointwise order comparison for two matched product triples. The
product and factor-order matrices and all endpoint/edge/uniqueness guards are
explicit. This does not yet quantify over a collected match graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchPointOrder

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchFactorOrderPoint PASoundness.PAtoCompactProductMatchProductLexPoint
open PASoundness.PAtoCompactProductMatchFactorEquality PASoundness.PAtoCompactProductIsoPointwiseLex

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceGuard : Formula := namedBoth (.member 0 30) (namedBoth (.member 1 31)
  (namedBoth (.member 2 32) (namedBoth (.member 0 50) (namedBoth (.member 1 51)
    (namedBoth (.member 2 52) (namedBoth (tripleFormula 30 31 32) (tripleFormula 50 51 52)))))))
def targetGuard : Formula := namedBoth (.member 42 33) (namedBoth (.member 43 34)
  (namedBoth (.member 44 35) (namedBoth (.member 42 53) (namedBoth (.member 43 54)
    (namedBoth (.member 44 55) (namedBoth (targetTriple 33 34 35) (targetTriple 53 54 55)))))))
def firstGuard : Formula := namedBoth (.member 0 30) (namedBoth (.member 0 50)
  (namedBoth (.member 42 33) (namedBoth (.member 42 53)
    (namedBoth (graphFormula 40 30 33) (graphFormula 40 50 53)))))
def secondGuard : Formula := namedBoth (.member 1 31) (namedBoth (.member 1 51)
  (namedBoth (.member 43 34) (namedBoth (.member 43 54)
    (namedBoth (graphFormula 41 31 34) (graphFormula 41 51 54)))))
def firstComparison : Formula := namedBoth (.imp (.member 50 30) (.member 53 33))
  (.imp (.member 53 33) (.member 50 30))
def secondComparison : Formula := namedBoth (.imp (.member 51 31) (.member 54 34))
  (.imp (.member 54 34) (.member 51 31))
def sourceLex : Formula := namedEither (.member 50 30) (namedBoth (.equal 30 50) (.member 51 31))
def targetLex : Formula := namedEither (.member 53 33) (namedBoth (.equal 33 53) (.member 54 34))
def sourceComparison : Formula := namedBoth (.imp (.member 52 32) sourceLex)
  (.imp sourceLex (.member 52 32))
def targetComparison : Formula := namedBoth (.imp (.member 55 35) targetLex)
  (.imp targetLex (.member 55 35))

theorem first_point_shape : firstPoint = .imp firstGuard firstComparison := by decide
theorem second_point_shape : secondPoint = .imp secondGuard secondComparison := by decide
theorem source_point_shape : sourcePoint = .imp sourceGuard sourceComparison := by decide
theorem target_point_shape : targetPoint = .imp targetGuard targetComparison := by decide

def assumptions : Formula := namedBoth productMatrix (namedBoth targetMatrix
  (namedBoth firstOrder (namedBoth secondOrder (namedBoth factorGuard
    (namedBoth sourceGuard (namedBoth targetGuard (namedBoth firstGuard secondGuard)))))))

/-- The two actual product comparisons, two factor-order comparisons, and
major-coordinate equality correspondence imply output-order correspondence. -/
def matched_point_order : KDerivation (imp assumptions.encode
    (iffCode (member 52 32) (member 55 35))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [assumptions.encode]
  have ha : Context Γ assumptions.encode := .head _ _
  have ha' : Context Γ (both productMatrix.encode (both targetMatrix.encode
      (both firstOrder.encode (both secondOrder.encode (both factorGuard.encode
        (both sourceGuard.encode (both targetGuard.encode (both firstGuard.encode secondGuard.encode)))))))) := by
    simpa [assumptions, namedBoth, Formula.not, Formula.encode, both, neg] using ha
  have hp := Context.conjunctionLeft ha'
  have htail := Context.conjunctionRight ha'
  have ht := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have ho₁ := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have ho₂ := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have heq := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have hsg := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have htg := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have hf₁ := Context.conjunctionLeft htail
  have hf₂ := Context.conjunctionRight htail
  have hfirstPoint : Context Γ firstPoint.encode := .mp ho₁ (.closed first_order_point)
  have hfirstImp : Context Γ (imp firstGuard.encode firstComparison.encode) := by
    simpa [first_point_shape, Formula.encode] using hfirstPoint
  have hfirst := Context.mp hf₁ hfirstImp
  have hmajor : Context Γ (iffCode (member 50 30) (member 53 33)) := by
    simpa [first_point_shape, firstComparison, iffCode, namedBoth, Formula.not, Formula.encode, both, neg] using hfirst
  have hsecondPoint : Context Γ secondPoint.encode := .mp ho₂ (.closed second_order_point)
  have hsecondImp : Context Γ (imp secondGuard.encode secondComparison.encode) := by
    simpa [second_point_shape, Formula.encode] using hsecondPoint
  have hsecond := Context.mp hf₂ hsecondImp
  have hminor : Context Γ (iffCode (member 51 31) (member 54 34)) := by
    simpa [second_point_shape, secondComparison, iffCode, namedBoth, Formula.not, Formula.encode, both, neg] using hsecond
  have hequal : Context Γ (iffCode (equal 30 50) (equal 33 53)) := by
    simpa [iffCode] using Context.mp heq (.closed equality_comparison)
  have hsourcePoint : Context Γ sourcePoint.encode := .mp hp (.closed source_point)
  have hsourceImp : Context Γ (imp sourceGuard.encode sourceComparison.encode) := by
    simpa [source_point_shape, Formula.encode] using hsourcePoint
  have hsource := Context.mp hsg hsourceImp
  have hsource' : Context Γ (iffCode (member 52 32)
      (lexCode (member 50 30) (equal 30 50) (member 51 31))) := by
    simpa [source_point_shape, sourceComparison, sourceLex, iffCode, lexCode,
      namedBoth, namedEither, Formula.not, Formula.encode, both, neg, either] using hsource
  have htargetPoint : Context Γ targetPoint.encode := .mp ht (.closed target_point)
  have htargetImp : Context Γ (imp targetGuard.encode targetComparison.encode) := by
    simpa [target_point_shape, Formula.encode] using htargetPoint
  have htarget := Context.mp htg htargetImp
  have htarget' : Context Γ (iffCode (member 55 35)
      (lexCode (member 53 33) (equal 33 53) (member 54 34))) := by
    simpa [target_point_shape, targetComparison, targetLex, iffCode, lexCode,
      namedBoth, namedEither, Formula.not, Formula.encode, both, neg, either] using htarget
  exact .mp htarget' (.mp hsource' (.mp hminor (.mp hequal (.mp hmajor
    (.closed (product_edge_order 30 50 31 51 33 53 34 54 32 52 35 55))))))

theorem matched_point_order_certificate : theoremCode (certificate matched_point_order) =
    imp assumptions.encode (iffCode (member 52 32) (member 55 35)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchPointOrder

#print axioms PASoundness.PAtoCompactProductMatchPointOrder.matched_point_order
#print axioms PASoundness.PAtoCompactProductMatchPointOrder.matched_point_order_certificate
