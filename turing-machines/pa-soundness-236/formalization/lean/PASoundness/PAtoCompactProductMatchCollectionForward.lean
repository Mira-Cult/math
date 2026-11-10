import PASoundness.PAtoCompactProductMatchCollectionOrderUnique
import PASoundness.PAtoCompactProductMatchForwardGraphAll

/-! Add forward coverage to the same collected graph already carrying
reverse coverage, forward uniqueness and order. Reverse uniqueness and the
standard quotient-equivalence packaging remain open. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchCollectionForward

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchFactorOrderPoint PASoundness.PAtoCompactProductMatchReverseGraphAll
open PASoundness.PAtoCompactProductMatchGraphForwardUniqueAll
open PASoundness.PAtoCompactProductMatchCollectionInsideConditional
open PASoundness.PAtoCompactProductMatchGraphOrder PASoundness.PAtoCompactProductMatchCollectionReverse
open PASoundness.PAtoCompactProductMatchCollectionOrderUnique PASoundness.PAtoCompactProductMatchForwardGraphAll

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def coveredGraph : Formula := namedBoth assembledGraph forwardCoverage

def collection_forward : KDerivation
    (imp extendedMatrices.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (existsCode 58 coveredGraph.encode))) := by
  have hpoint : KDerivation (imp extendedMatrices.encode (imp assembledGraph.encode coveredGraph.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [assembledGraph.encode,extendedMatrices.encode]
    have hg : Context Γ assembledGraph.encode := .head _ _
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
    have hg' : Context Γ (both retainedGraph.encode (both forwardUniqueAll.encode outputOrder.encode)) := by
      simpa [assembledGraph, namedBoth, Formula.not, Formula.encode, both, neg] using hg
    have hr := Context.conjunctionLeft hg'
    have hr' : Context Γ (both actualMatch.encode reverseCoverage.encode) := by
      simpa [retainedGraph, namedBoth, Formula.not, Formula.encode, both, neg] using hr
    have hmatch := Context.conjunctionLeft hr'
    have hf := Context.mp hmatch (Context.mp ht (Context.mp hb₂
      (Context.mp hb₁ (Context.mp hp (.closed forward_graph_all)))))
    simpa [Γ, coveredGraph, namedBoth, Formula.not, Formula.encode, both, neg] using
      Context.conjunctionIntro hg hf
  have hlift := conditionalExistsCongr 58 (extendedMatrices.vacuity 58 (by decide)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 2 81 77 78 72 64 73 59 75
  let Γ := [C,extendedMatrices.encode]
  have hc : Context Γ C := .head _ _
  have hm : Context Γ extendedMatrices.encode := .hypothesis (by simp [Γ])
  have hex := Context.mp hc (Context.mp hm (.closed collection_order_unique))
  simpa [Γ, C] using Context.mp hex (Context.mp hm (.closed hlift))

theorem collection_forward_certificate : theoremCode (certificate collection_forward) =
    imp extendedMatrices.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (existsCode 58 coveredGraph.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchCollectionForward

#print axioms PASoundness.PAtoCompactProductMatchCollectionForward.collection_forward
#print axioms PASoundness.PAtoCompactProductMatchCollectionForward.collection_forward_certificate
