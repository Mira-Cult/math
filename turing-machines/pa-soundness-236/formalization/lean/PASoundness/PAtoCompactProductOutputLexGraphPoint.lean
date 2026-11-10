import PASoundness.PAtoCompactProductOutputLexPathOrder
import PASoundness.PAtoCompactProductOutputForwardUnique
import PASoundness.PAtoCompactProductOutputActualPoint
import PASoundness.PAtoCompactScopedActiveReplace

/-! Pointwise lex order for two guarded triples of one actual output graph.
The source product matrix and supplied output order remain explicit. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputLexGraphPoint

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactMultiplicationSingleTripleExtension
open PASoundness.PAtoCompactProductMatchFactorOrderPoint PASoundness.PAtoCompactProductOutputReverseCoverage
open PASoundness.PAtoCompactProductOutputImageRelation PASoundness.PAtoCompactProductOutputActualPoint
open PASoundness.PAtoCompactProductOutputForwardUnique PASoundness.PAtoCompactProductOutputLexPointOrder
open PASoundness.PAtoCompactProductOutputLexBodyOrder PASoundness.PAtoCompactProductOutputLexPathOrder

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def otherPoint : Formula := replace 33 55 (replace 31 51 (replace 30 50 selectedPoint))
def otherActualPath : Formula := replace 33 55 (replace 31 51 (replace 30 50 actualPath))
def otherGuard : Formula := namedBoth (.member 43 50) (namedBoth (.member 44 51) (.member 42 55))
def otherTriple : Formula := tripleAt 58 50 51 55
def graphGuard : Formula := namedBoth relocatedMatrix (namedBoth firstOrder (namedBoth actualInvariant
  (namedBoth (.member 43 30) (namedBoth (.member 44 31) (namedBoth (.member 43 50)
    (namedBoth (.member 44 51) (namedBoth (.member 42 33) (namedBoth (.member 42 55)
      (namedBoth selectedTriple otherTriple)))))))))

theorem other_point_shape : otherPoint = .imp otherGuard
  (namedBoth (.imp otherTriple otherActualPath) (.imp otherActualPath otherTriple)) := by decide

def other_instance : KDerivation (imp actualInvariant.encode otherPoint.encode) := by
  let F : Formula := .imp actualInvariant selectedPoint
  have h0 : KDerivation F.encode := by simpa [F, CompactNamed.Formula.encode] using actual_instance
  have h1 := replace_derivation 30 50 F (by decide) (by decide) h0
  have h2 := replace_derivation 31 51 (replace 30 50 F) (by decide) (by decide) h1
  have h3 := replace_derivation 33 55 (replace 31 51 (replace 30 50 F)) (by decide) (by decide) h2
  have hs : replace 33 55 (replace 31 51 (replace 30 50 F)) = .imp actualInvariant otherPoint := by decide
  rw [hs] at h3
  simpa [CompactNamed.Formula.encode] using h3

def other_path_to_image : KDerivation (imp otherActualPath.encode otherInput.encode) := by
  let F : Formula := .imp actualPath imagePath
  have h0 : KDerivation F.encode := by simpa [F, CompactNamed.Formula.encode] using actual_path_to_image
  have h1 := replace_derivation 30 50 F (by decide) (by decide) h0
  have h2 := replace_derivation 31 51 (replace 30 50 F) (by decide) (by decide) h1
  have h3 := replace_derivation 33 55 (replace 31 51 (replace 30 50 F)) (by decide) (by decide) h2
  have hs : replace 33 55 (replace 31 51 (replace 30 50 F)) = .imp otherActualPath otherInput := by decide
  rw [hs] at h3
  simpa only [CompactNamed.Formula.encode] using h3

/-- Under both actual target triples, target output order agrees with factor
lex order in the displayed direction. -/
def graph_point_order : KDerivation (imp graphGuard.encode targetComparison.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [graphGuard.encode]
  have hg : Context Γ graphGuard.encode := .head _ _
  have hg' : Context Γ (both relocatedMatrix.encode (both firstOrder.encode (both actualInvariant.encode
      (both (member 43 30) (both (member 44 31) (both (member 43 50) (both (member 44 51)
        (both (member 42 33) (both (member 42 55) (both selectedTriple.encode otherTriple.encode)))))))))) := by
    simpa [graphGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hm := Context.conjunctionLeft hg'
  have t := Context.conjunctionRight hg'
  have ho := Context.conjunctionLeft t
  have t := Context.conjunctionRight t
  have hi := Context.conjunctionLeft t
  have t := Context.conjunctionRight t
  have hx := Context.conjunctionLeft t
  have t := Context.conjunctionRight t
  have hy := Context.conjunctionLeft t
  have t := Context.conjunctionRight t
  have hx' := Context.conjunctionLeft t
  have t := Context.conjunctionRight t
  have hy' := Context.conjunctionLeft t
  have t := Context.conjunctionRight t
  have hz := Context.conjunctionLeft t
  have t := Context.conjunctionRight t
  have hz' := Context.conjunctionLeft t
  have hedges := Context.conjunctionRight t
  have hsource : Context Γ selectedGuard.encode := by
    simpa [selectedGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hx (Context.conjunctionIntro hy hz)
  have hother : Context Γ otherGuard.encode := by
    simpa [otherGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hx' (Context.conjunctionIntro hy' hz')
  have hp := Context.mp hsource (Context.mp hi (.closed actual_instance))
  have hp' : Context Γ (both (imp selectedTriple.encode actualPath.encode)
      (imp actualPath.encode selectedTriple.encode)) := by
    simpa [selectedPoint, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hp
  have hq0 : Context Γ otherPoint.encode := .mp hi (.closed other_instance)
  rw [other_point_shape] at hq0
  have hq : Context Γ (namedBoth (.imp otherTriple otherActualPath) (.imp otherActualPath otherTriple)).encode :=
    .mp hother hq0
  have hq' : Context Γ (both (imp otherTriple.encode otherActualPath.encode)
      (imp otherActualPath.encode otherTriple.encode)) := by
    simpa [namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hq
  have hpath := Context.mp (Context.conjunctionLeft hedges) (Context.conjunctionLeft hp')
  have hpath' := Context.mp (Context.conjunctionRight hedges) (Context.conjunctionLeft hq')
  have himage := Context.mp hpath (.closed actual_path_to_image)
  have himage' := Context.mp hpath' (.closed other_path_to_image)
  have hguard : Context Γ PAtoCompactProductOutputLexBodyOrder.guard.encode := by
    simpa [PAtoCompactProductOutputLexBodyOrder.guard, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using Context.conjunctionIntro hm (Context.conjunctionIntro ho
        (Context.conjunctionIntro hx (Context.conjunctionIntro hy (Context.conjunctionIntro hx' hy'))))
  exact .mp himage' (.mp himage (.mp hguard (.closed path_order)))

theorem graph_point_order_certificate : theoremCode (certificate graph_point_order) =
    imp graphGuard.encode targetComparison.encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputLexGraphPoint

#print axioms PASoundness.PAtoCompactProductOutputLexGraphPoint.graph_point_order
#print axioms PASoundness.PAtoCompactProductOutputLexGraphPoint.graph_point_order_certificate
