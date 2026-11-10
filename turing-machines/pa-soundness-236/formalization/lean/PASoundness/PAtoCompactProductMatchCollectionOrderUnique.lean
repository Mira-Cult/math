import PASoundness.PAtoCompactProductMatchCollectionReverse
import PASoundness.PAtoCompactProductMatchGraphForwardUniqueAll

/-! Keep reverse coverage, guarded forward uniqueness and order on the same
collected graph. This is not yet a full bijection or quotient equivalence. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchCollectionOrderUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchTargetOutput PASoundness.PAtoCompactProductMatchFactorOrderPoint
open PASoundness.PAtoCompactProductMatchCollectionInsideConditional
open PASoundness.PAtoCompactProductMatchGraphOrder PASoundness.PAtoCompactProductMatchCollectionReverse
open PASoundness.PAtoCompactProductMatchReverseGraphAll
open PASoundness.PAtoCompactProductMatchGraphForwardUniqueAll

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def extendedMatrices : Formula := namedBoth assumptions (namedBoth firstOrder secondOrder)
def assembledGraph : Formula := namedBoth retainedGraph (namedBoth forwardUniqueAll outputOrder)

def collection_order_unique : KDerivation
    (imp extendedMatrices.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (existsCode 58 assembledGraph.encode))) := by
  have hpoint : KDerivation (imp extendedMatrices.encode (imp retainedGraph.encode assembledGraph.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [retainedGraph.encode,extendedMatrices.encode]
    have hr : Context Γ retainedGraph.encode := .head _ _
    have hm : Context Γ extendedMatrices.encode := .hypothesis (by simp [Γ])
    have hm' : Context Γ (both assumptions.encode (both firstOrder.encode secondOrder.encode)) := by
      simpa [extendedMatrices, namedBoth, Formula.not, Formula.encode, both, neg] using hm
    have ha := Context.conjunctionLeft hm'
    have ho₁ := Context.conjunctionLeft (Context.conjunctionRight hm')
    have ho₂ := Context.conjunctionRight (Context.conjunctionRight hm')
    have ha' : Context Γ (both productMatrix.encode (both firstBijection.encode
        (both secondBijection.encode targetMatrix.encode))) := by
      simpa [assumptions, namedBoth, Formula.not, Formula.encode, both, neg] using ha
    have hp := Context.conjunctionLeft ha'
    have hb₁ := Context.conjunctionLeft (Context.conjunctionRight ha')
    have ht := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight ha'))
    have hr' : Context Γ (both actualMatch.encode reverseCoverage.encode) := by
      simpa [retainedGraph, namedBoth, Formula.not, Formula.encode, both, neg] using hr
    have hg := Context.conjunctionLeft hr'
    have hu := Context.mp hg (.closed forward_unique_all)
    have hmat : Context Γ matrices.encode := by
      have h := Context.conjunctionIntro hp (Context.conjunctionIntro ht (Context.conjunctionIntro hb₁
        (Context.conjunctionIntro ho₁ ho₂)))
      simpa [matrices, namedBoth, Formula.not, Formula.encode, both, neg] using h
    have ho := Context.mp hg (Context.mp hmat (.closed graph_order))
    simpa [Γ, assembledGraph, namedBoth, Formula.not, Formula.encode, both, neg] using
      Context.conjunctionIntro hr (Context.conjunctionIntro hu ho)
  have hlift := conditionalExistsCongr 58 (extendedMatrices.vacuity 58 (by decide)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 2 81 77 78 72 64 73 59 75
  let Γ := [C,extendedMatrices.encode]
  have hc : Context Γ C := .head _ _
  have hm : Context Γ extendedMatrices.encode := .hypothesis (by simp [Γ])
  have hm' : Context Γ (both assumptions.encode (both firstOrder.encode secondOrder.encode)) := by
    simpa [extendedMatrices, namedBoth, Formula.not, Formula.encode, both, neg] using hm
  have hex := Context.mp hc (Context.mp (Context.conjunctionLeft hm') (.closed collection_reverse))
  simpa [Γ, C] using Context.mp hex (Context.mp hm (.closed hlift))

theorem collection_order_unique_certificate : theoremCode (certificate collection_order_unique) =
    imp extendedMatrices.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (existsCode 58 assembledGraph.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchCollectionOrderUnique

#print axioms PASoundness.PAtoCompactProductMatchCollectionOrderUnique.collection_order_unique
#print axioms PASoundness.PAtoCompactProductMatchCollectionOrderUnique.collection_order_unique_certificate
