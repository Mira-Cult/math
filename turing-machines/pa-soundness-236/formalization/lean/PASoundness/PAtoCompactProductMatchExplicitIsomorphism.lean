import PASoundness.PAtoCompactProductMatchCollectionComplete
import PASoundness.PAtoCompactProductMatchForwardBijectionClause
import PASoundness.PAtoCompactProductMatchReverseBijectionClause

/-! Construct an explicit guarded product order-isomorphism formula on one
collected graph. Alignment with the standard `equivAt` syntax is separate. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchExplicitIsomorphism

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactProductMatchGraphOrder PASoundness.PAtoCompactProductMatchReverseGraphAll
open PASoundness.PAtoCompactProductMatchForwardGraphAll PASoundness.PAtoCompactProductMatchGraphForwardUniqueAll
open PASoundness.PAtoCompactProductMatchGraphReverseUnique PASoundness.PAtoCompactProductMatchCollectionReverse
open PASoundness.PAtoCompactProductMatchCollectionOrderUnique PASoundness.PAtoCompactProductMatchCollectionForward
open PASoundness.PAtoCompactProductMatchCollectionComplete PASoundness.PAtoCompactProductMatchForwardBijectionClause
open PASoundness.PAtoCompactProductMatchReverseBijectionClause

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def isoBody : Formula := namedBoth (namedBoth forwardClause reverseClause) outputOrder
def explicitIsomorphism : Formula := .ex 58 isoBody

def complete_to_iso : KDerivation (imp completeGraph.encode isoBody.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [completeGraph.encode]
  have hc : Context Γ completeGraph.encode := .head _ _
  have hc' : Context Γ (both coveredGraph.encode reverseUniqueAll.encode) := by
    simpa [completeGraph, namedBoth, Formula.not, Formula.encode, both, neg] using hc
  have hg := Context.conjunctionLeft hc'
  have hru := Context.conjunctionRight hc'
  have hg' : Context Γ (both assembledGraph.encode forwardCoverage.encode) := by
    simpa [coveredGraph, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have ha := Context.conjunctionLeft hg'
  have hfc := Context.conjunctionRight hg'
  have ha' : Context Γ (both retainedGraph.encode (both forwardUniqueAll.encode outputOrder.encode)) := by
    simpa [assembledGraph, namedBoth, Formula.not, Formula.encode, both, neg] using ha
  have hr := Context.conjunctionLeft ha'
  have hfu := Context.conjunctionLeft (Context.conjunctionRight ha')
  have ho := Context.conjunctionRight (Context.conjunctionRight ha')
  have hr' : Context Γ (both actualMatch.encode reverseCoverage.encode) := by
    simpa [retainedGraph, namedBoth, Formula.not, Formula.encode, both, neg] using hr
  have hrc := Context.conjunctionRight hr'
  have hf := Context.mp hfc (Context.mp hfu (.closed coverage_unique_to_forward))
  have hb := Context.mp hrc (Context.mp hru (.closed coverage_unique_to_reverse))
  simpa [Γ, isoBody, namedBoth, Formula.not, Formula.encode, both, neg] using
    Context.conjunctionIntro (Context.conjunctionIntro hf hb) ho

/-- Candidate source and both product/factor isomorphism matrices produce one
graph satisfying the explicit forward, reverse and order clauses. -/
def product_explicit_isomorphism : KDerivation
    (imp extendedMatrices.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      explicitIsomorphism.encode)) := by
  have hmap := existsCongr 58 complete_to_iso
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 2 81 77 78 72 64 73 59 75
  let Γ := [C,extendedMatrices.encode]
  have hc : Context Γ C := .head _ _
  have hm : Context Γ extendedMatrices.encode := .hypothesis (by simp [Γ])
  have hex := Context.mp hc (Context.mp hm (.closed collection_complete))
  simpa [Γ, C, explicitIsomorphism, Formula.encode] using Context.mp hex (.closed hmap)

theorem product_explicit_isomorphism_certificate : theoremCode (certificate product_explicit_isomorphism) =
    imp extendedMatrices.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      explicitIsomorphism.encode) := certificate_correct _

end PASoundness.PAtoCompactProductMatchExplicitIsomorphism

#print axioms PASoundness.PAtoCompactProductMatchExplicitIsomorphism.complete_to_iso
#print axioms PASoundness.PAtoCompactProductMatchExplicitIsomorphism.product_explicit_isomorphism
#print axioms PASoundness.PAtoCompactProductMatchExplicitIsomorphism.product_explicit_isomorphism_certificate
