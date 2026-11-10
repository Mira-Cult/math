import PASoundness.PAtoCompactProductMatchCollectionCandidate
import PASoundness.PAtoCompactProductMatchReverseGraphAll

/-! Retain the collected match graph and its reverse-coverage clause on the
same graph witness. Source candidacy and all four product/factor matrices
remain explicit. This is not a full bijection or quotient congruence. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchCollectionReverse

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchCollectionInsideConditional
open PASoundness.PAtoCompactProductMatchCollectionCandidate
open PASoundness.PAtoCompactProductMatchGraphOrder PASoundness.PAtoCompactProductMatchReverseGraphAll

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def retainedGraph : Formula := namedBoth actualMatch reverseCoverage

def collection_reverse : KDerivation
    (imp assumptions.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (existsCode 58 retainedGraph.encode))) := by
  have hpoint : KDerivation (imp assumptions.encode (imp actualMatch.encode retainedGraph.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [actualMatch.encode,assumptions.encode]
    have ha : Context Γ actualMatch.encode := .head _ _
    have hm : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
    have hm' : Context Γ (both productMatrix.encode (both firstBijection.encode
        (both secondBijection.encode targetMatrix.encode))) := by
      simpa [assumptions, namedBoth, Formula.not, Formula.encode, both, neg] using hm
    have hp := Context.conjunctionLeft hm'
    have hb₁ := Context.conjunctionLeft (Context.conjunctionRight hm')
    have hb₂ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hm'))
    have ht := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hm'))
    have hr := Context.mp ha (Context.mp ht (Context.mp hb₂
      (Context.mp hb₁ (Context.mp hp (.closed reverse_graph_all)))))
    simpa [Γ, retainedGraph, namedBoth, Formula.not, Formula.encode, both, neg] using
      Context.conjunctionIntro ha hr
  have hlift := conditionalExistsCongr 58 (assumptions.vacuity 58 (by decide)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 2 81 77 78 72 64 73 59 75
  let Γ := [C,assumptions.encode]
  have hc : Context Γ C := .head _ _
  have hm : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hex := Context.mp hc (Context.mp hm (.closed source_collection))
  simpa [Γ, C, actualMatch] using Context.mp hex (Context.mp hm (.closed hlift))

theorem collection_reverse_certificate : theoremCode (certificate collection_reverse) =
    imp assumptions.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (existsCode 58 retainedGraph.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchCollectionReverse

#print axioms PASoundness.PAtoCompactProductMatchCollectionReverse.collection_reverse
#print axioms PASoundness.PAtoCompactProductMatchCollectionReverse.collection_reverse_certificate
