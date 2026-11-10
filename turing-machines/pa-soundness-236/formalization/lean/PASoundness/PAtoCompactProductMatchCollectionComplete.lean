import PASoundness.PAtoCompactProductMatchCollectionForward
import PASoundness.PAtoCompactProductMatchGraphReverseUnique

/-! Retain both coverage and uniqueness directions and the guarded order
clause on one collected graph. The standard equivalence formula still needs
an explicit syntactic packaging proof. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchCollectionComplete

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchTargetOutput PASoundness.PAtoCompactProductMatchFactorOrderPoint
open PASoundness.PAtoCompactProductMatchCollectionInsideConditional PASoundness.PAtoCompactProductMatchGraphOrder
open PASoundness.PAtoCompactProductMatchReverseGraphAll PASoundness.PAtoCompactProductMatchForwardGraphAll
open PASoundness.PAtoCompactProductMatchGraphForwardUniqueAll PASoundness.PAtoCompactProductMatchCollectionReverse
open PASoundness.PAtoCompactProductMatchCollectionOrderUnique PASoundness.PAtoCompactProductMatchCollectionForward
open PASoundness.PAtoCompactProductMatchGraphReverseUnique

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def completeGraph : Formula := namedBoth coveredGraph reverseUniqueAll

def collection_complete : KDerivation
    (imp extendedMatrices.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (existsCode 58 completeGraph.encode))) := by
  have hpoint : KDerivation (imp extendedMatrices.encode (imp coveredGraph.encode completeGraph.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [coveredGraph.encode,extendedMatrices.encode]
    have hg : Context Γ coveredGraph.encode := .head _ _
    have hm : Context Γ extendedMatrices.encode := .hypothesis (by simp [Γ])
    have hm' : Context Γ (both assumptions.encode (both firstOrder.encode secondOrder.encode)) := by
      simpa [extendedMatrices, namedBoth, Formula.not, Formula.encode, both, neg] using hm
    have ha := Context.conjunctionLeft hm'
    have ha' : Context Γ (both productMatrix.encode (both firstBijection.encode
        (both secondBijection.encode targetMatrix.encode))) := by
      simpa [assumptions, namedBoth, Formula.not, Formula.encode, both, neg] using ha
    have hp := Context.conjunctionLeft ha'
    have hb₁ := Context.conjunctionLeft (Context.conjunctionRight ha')
    have hb₂ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight ha'))
    have ht := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight ha'))
    have hg' : Context Γ (both assembledGraph.encode forwardCoverage.encode) := by
      simpa [coveredGraph, namedBoth, Formula.not, Formula.encode, both, neg] using hg
    have has := Context.conjunctionLeft hg'
    have has' : Context Γ (both retainedGraph.encode (both forwardUniqueAll.encode outputOrder.encode)) := by
      simpa [assembledGraph, namedBoth, Formula.not, Formula.encode, both, neg] using has
    have hr := Context.conjunctionLeft has'
    have hr' : Context Γ (both actualMatch.encode reverseCoverage.encode) := by
      simpa [retainedGraph, namedBoth, Formula.not, Formula.encode, both, neg] using hr
    have hmatch := Context.conjunctionLeft hr'
    have hmat : Context Γ PASoundness.PAtoCompactProductMatchGraphReverseUnique.matrices.encode := by
      have h := Context.conjunctionIntro hp (Context.conjunctionIntro ht (Context.conjunctionIntro hb₁ hb₂))
      simpa [PASoundness.PAtoCompactProductMatchGraphReverseUnique.matrices,
        namedBoth, Formula.not, Formula.encode, both, neg] using h
    have hu := Context.mp hmatch (Context.mp hmat (.closed reverse_graph_unique))
    simpa [Γ, completeGraph, namedBoth, Formula.not, Formula.encode, both, neg] using
      Context.conjunctionIntro hg hu
  have hlift := conditionalExistsCongr 58 (extendedMatrices.vacuity 58 (by decide)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 2 81 77 78 72 64 73 59 75
  let Γ := [C,extendedMatrices.encode]
  have hc : Context Γ C := .head _ _
  have hm : Context Γ extendedMatrices.encode := .hypothesis (by simp [Γ])
  have hex := Context.mp hc (Context.mp hm (.closed collection_forward))
  simpa [Γ, C] using Context.mp hex (Context.mp hm (.closed hlift))

theorem collection_complete_certificate : theoremCode (certificate collection_complete) =
    imp extendedMatrices.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (existsCode 58 completeGraph.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchCollectionComplete

#print axioms PASoundness.PAtoCompactProductMatchCollectionComplete.collection_complete
#print axioms PASoundness.PAtoCompactProductMatchCollectionComplete.collection_complete_certificate
