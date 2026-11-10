import PASoundness.PAtoCompactMultiplicationFirstBranchSplit
import PASoundness.PAtoCompactProductOldSuffixExclusion
import PASoundness.PAtoCompactTransitiveClosure

/-! Recover a suffix-map edge from a top-major product-graph query, conditional
on the supplied clean-old-graph major-endpoint lemma. This does not assert the
cleanliness premise, construct the graph, prove multiplication totality, or
identify independently represented ordered pairs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTopQueryConditional
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationOldTripleIntro
open PASoundness.PAtoCompactMultiplicationRowQueryFirst
open PASoundness.PAtoCompactMultiplicationRowQueryFirstExists
open PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
open PASoundness.PAtoCompactMultiplicationFirstBranchSplit
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Given a finite K major-endpoint proof for the clean old graph, any new
triple whose major is 30 has its second and output coordinates connected by
the SAME suffix-map graph 6. The target bound must be proved separately. -/
def top_query_of_old_endpoint
    (hOld : KDerivation (imp PASoundness.PAtoCompactProductOldSuffixExclusion.oldClean.encode
      (imp oldTriple.encode (member 30 3)))) :
    KDerivation (imp PASoundness.PAtoCompactProductOldSuffixExclusion.oldClean.encode
      (imp (noGarbage 64).encode (imp (equal 3 30)
        (imp queriedTriple.encode (both (member 31 4) (graphFormula 6 4 5).encode))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let C := PASoundness.PAtoCompactProductOldSuffixExclusion.oldClean.encode
  let Γ := [queriedTriple.encode,equal 3 30,(noGarbage 64).encode,C]
  have ht : Context Γ queriedTriple.encode := .head _ _
  have he : Context Γ (equal 3 30) := .hypothesis (by simp [Γ])
  have hn : Context Γ (noGarbage 64).encode := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hcases : Context Γ (either oldTriple.encode queriedNewRow.encode) := by
    have h := Context.mp ht (Context.mp hn (.closed first_branch_split))
    simpa [branchResult,namedEither,Formula.not,Formula.encode,either,neg] using h
  apply Context.disjunctionElim hcases
  · let Δ := oldTriple.encode :: Γ
    have ho : Context Δ oldTriple.encode := .head _ _
    have hm : Context Δ (member 30 3) := .mp ho (.mp (.under hc _) (.closed hOld))
    have hs : Context Δ (member 30 30) := .mp (.under he _)
      (.mp hm (.closed (memberRightEquality 30 3 30)))
    exact Context.explode _ (.mp hs (.closed (self_membership_implies_code_one 30)))
  · let Δ := queriedNewRow.encode :: Γ
    have hr : Context Δ queryResult.encode := .mp (.head _ _) (.closed query_exists_elim)
    have h : Context Δ (both (equal 3 30) (both (member 31 4) (graphFormula 6 4 5).encode)) := by
      simpa [queryResult,namedBoth,Formula.not,Formula.encode,both,neg] using hr
    exact Context.conjunctionRight h

theorem top_query_of_old_endpoint_certificate
    (hOld : KDerivation (imp PASoundness.PAtoCompactProductOldSuffixExclusion.oldClean.encode
      (imp oldTriple.encode (member 30 3)))) :
    theoremCode (certificate (top_query_of_old_endpoint hOld)) =
      imp PASoundness.PAtoCompactProductOldSuffixExclusion.oldClean.encode
        (imp (noGarbage 64).encode (imp (equal 3 30)
          (imp queriedTriple.encode (both (member 31 4) (graphFormula 6 4 5).encode)))) :=
  certificate_correct (top_query_of_old_endpoint hOld)
end PASoundness.PAtoCompactMultiplicationTopQueryConditional
#print axioms PASoundness.PAtoCompactMultiplicationTopQueryConditional.top_query_of_old_endpoint
#print axioms PASoundness.PAtoCompactMultiplicationTopQueryConditional.top_query_of_old_endpoint_certificate
