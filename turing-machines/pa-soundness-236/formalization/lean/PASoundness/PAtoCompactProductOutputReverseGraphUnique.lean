import PASoundness.PAtoCompactProductOutputReversePathUnique
import PASoundness.PAtoCompactProductOutputForwardUnique
import PASoundness.PAtoCompactProductOutputActualPoint
import PASoundness.PAtoCompactScopedActiveReplace

/-! Reverse coordinate uniqueness for two guarded triples in the same
supplied target graph. Matrix/bijection, invariant, target membership and
both factor-domain guards remain explicit. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputReverseGraphUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactMultiplicationSingleTripleExtension
open PASoundness.PAtoCompactProductOutputCollectionInsideConditional PASoundness.PAtoCompactProductOutputActualPoint
open PASoundness.PAtoCompactProductOutputForwardUnique PASoundness.PAtoCompactProductOutputReversePointUnique
open PASoundness.PAtoCompactProductOutputImageRelation
open PASoundness.PAtoCompactProductOutputReversePathUnique

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def rivalPoint : Formula := replace 31 53 (replace 30 51 selectedPoint)
def rivalActualPath : Formula := replace 31 53 (replace 30 51 actualPath)
def rivalGuard : Formula := replace 31 53 (replace 30 51 selectedGuard)
def rivalTriple : Formula := tripleAt 58 51 53 33
def graphGuard : Formula := namedBoth assumptions (namedBoth actualInvariant (namedBoth (.member 42 33)
  (namedBoth (.member 43 30) (namedBoth (.member 44 31) (namedBoth (.member 43 51)
    (namedBoth (.member 44 53) (namedBoth selectedTriple rivalTriple)))))))

theorem rival_point_shape : rivalPoint = .imp rivalGuard
    (namedBoth (.imp rivalTriple rivalActualPath) (.imp rivalActualPath rivalTriple)) := by decide
theorem rival_guard_shape : rivalGuard = namedBoth (.member 43 51)
    (namedBoth (.member 44 53) (.member 42 33)) := by decide

def rival_instance : KDerivation (imp actualInvariant.encode rivalPoint.encode) := by
  let F : Formula := .imp actualInvariant selectedPoint
  have h0 : KDerivation F.encode := by simpa [F, CompactNamed.Formula.encode] using actual_instance
  have h1 := replace_derivation 30 51 F (by decide) (by decide) h0
  have h2 := replace_derivation 31 53 (replace 30 51 F) (by decide) (by decide) h1
  have hs : replace 31 53 (replace 30 51 F) = .imp actualInvariant rivalPoint := by decide
  rw [hs] at h2
  simpa [CompactNamed.Formula.encode] using h2

def rival_path_to_image : KDerivation (imp rivalActualPath.encode
    PAtoCompactProductOutputReversePathUnique.rivalInput.encode) := by
  let F : Formula := .imp actualPath imagePath
  have h0 : KDerivation F.encode := by simpa [F, CompactNamed.Formula.encode] using actual_path_to_image
  have h1 := replace_derivation 30 51 F (by decide) (by decide) h0
  have h2 := replace_derivation 31 53 (replace 30 51 F) (by decide) (by decide) h1
  have hs : replace 31 53 (replace 30 51 F) = .imp rivalActualPath
      PAtoCompactProductOutputReversePathUnique.rivalInput := by decide
  rw [hs] at h2
  simpa only [CompactNamed.Formula.encode] using h2

/-- If both guarded factor pairs give the same target in this graph, the
rival coordinates equal the selected coordinates. -/
def reverse_graph_unique : KDerivation (imp graphGuard.encode
    (both (equal 51 30) (equal 53 31))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [graphGuard.encode]
  have hg : Context Γ graphGuard.encode := .head _ _
  have hg' : Context Γ (both assumptions.encode (both actualInvariant.encode (both (member 42 33)
      (both (member 43 30) (both (member 44 31) (both (member 43 51)
        (both (member 44 53) (both selectedTriple.encode rivalTriple.encode)))))))) := by
    simpa [graphGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have ha := Context.conjunctionLeft hg'
  have hi := Context.conjunctionLeft (Context.conjunctionRight hg')
  have ht := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg'))
  have hx := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))
  have hy := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))))
  have hx' := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))))
  have hy' := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))))))
  have hedges := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))))))
  have hpointGuard : Context Γ pointGuard.encode := by
    simpa [pointGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro ha (Context.conjunctionIntro hx (Context.conjunctionIntro hy (Context.conjunctionIntro hx' hy')))
  have hguard : Context Γ selectedGuard.encode := by
    simpa [selectedGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hx (Context.conjunctionIntro hy ht)
  have hguard' : Context Γ rivalGuard.encode := by
    simpa [rival_guard_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hx' (Context.conjunctionIntro hy' ht)
  have hp := Context.mp hguard (Context.mp hi (.closed actual_instance))
  have hp' : Context Γ (both (imp selectedTriple.encode actualPath.encode)
      (imp actualPath.encode selectedTriple.encode)) := by
    simpa [selectedPoint, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hp
  have hr0 : Context Γ rivalPoint.encode := .mp hi (.closed rival_instance)
  rw [rival_point_shape] at hr0
  have hr : Context Γ (namedBoth (.imp rivalTriple rivalActualPath) (.imp rivalActualPath rivalTriple)).encode :=
    .mp hguard' hr0
  have hr' : Context Γ (both (imp rivalTriple.encode rivalActualPath.encode)
      (imp rivalActualPath.encode rivalTriple.encode)) := by
    simpa [namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hr
  have hpath := Context.mp (Context.conjunctionLeft hedges) (Context.conjunctionLeft hp')
  have hpath' := Context.mp (Context.conjunctionRight hedges) (Context.conjunctionLeft hr')
  have himage := Context.mp hpath (.closed actual_path_to_image)
  have himage' := Context.mp hpath' (.closed rival_path_to_image)
  have hresult := Context.mp himage' (Context.mp himage (Context.mp hpointGuard (.closed path_unique)))
  simpa [equalities, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hresult

theorem reverse_graph_unique_certificate : theoremCode (certificate reverse_graph_unique) =
    imp graphGuard.encode (both (equal 51 30) (equal 53 31)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputReverseGraphUnique

#print axioms PASoundness.PAtoCompactProductOutputReverseGraphUnique.rival_instance
#print axioms PASoundness.PAtoCompactProductOutputReverseGraphUnique.rival_path_to_image
#print axioms PASoundness.PAtoCompactProductOutputReverseGraphUnique.reverse_graph_unique
#print axioms PASoundness.PAtoCompactProductOutputReverseGraphUnique.reverse_graph_unique_certificate
