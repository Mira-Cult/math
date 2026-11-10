import PASoundness.PAtoCompactMultiplicationFirstBranchSplit
import PASoundness.PAtoCompactTransitiveClosure

/-! Recover the old product triple from an actual new-graph triple when its
major coordinate belongs to the old major domain. The no-garbage invariant
is explicit. The proof uses the same-edge branch extractor, not uniqueness
or equality of distinct pair representatives. It does not construct graphs or
prove multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationOldTripleRecover
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationOldTripleIntro
open PASoundness.PAtoCompactMultiplicationRowQueryFirst
open PASoundness.PAtoCompactMultiplicationRowQueryFirstExists
open PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
open PASoundness.PAtoCompactMultiplicationFirstBranchSplit
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- An old-domain queried major coordinate cannot belong to the new top row.
Therefore the exact queried triple already belonged to old graph 10. -/
def recover_old_triple : KDerivation (imp (member 30 3)
    (imp (noGarbage 64).encode (imp queriedTriple.encode oldTriple.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [queriedTriple.encode,(noGarbage 64).encode,member 30 3]
  have ht : Context Γ queriedTriple.encode := .head _ _
  have hn : Context Γ (noGarbage 64).encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 30 3) := .hypothesis (by simp [Γ])
  have hcases : Context Γ (either oldTriple.encode queriedNewRow.encode) := by
    have hh := Context.mp ht (Context.mp hn (.closed first_branch_split))
    simpa [branchResult,namedEither,Formula.not,Formula.encode,either,neg] using hh
  apply Context.disjunctionElim hcases
  · exact Context.head _ _
  · let Δ := queriedNewRow.encode :: Γ
    have hrow : Context Δ queriedNewRow.encode := .head _ _
    have hr : Context Δ queryResult.encode := .mp hrow (.closed query_exists_elim)
    have hc : Context Δ (both (equal 3 30)
        (both (member 31 4) (PASoundness.PAtoCompactOrderIsomorphism.graphFormula 6 4 5).encode)) := by
      simpa [queryResult,namedBoth,Formula.not,Formula.encode,both,neg] using hr
    have hs : Context Δ (member 30 30) := .mp (Context.conjunctionLeft hc)
      (.mp (.under hm _) (.closed (memberRightEquality 30 3 30)))
    exact Context.explode oldTriple.encode (.mp hs (.closed (self_membership_implies_code_one 30)))

theorem recover_old_triple_certificate : theoremCode (certificate recover_old_triple) =
    imp (member 30 3) (imp (noGarbage 64).encode (imp queriedTriple.encode oldTriple.encode)) :=
  certificate_correct recover_old_triple
end PASoundness.PAtoCompactMultiplicationOldTripleRecover
#print axioms PASoundness.PAtoCompactMultiplicationOldTripleRecover.recover_old_triple
#print axioms PASoundness.PAtoCompactMultiplicationOldTripleRecover.recover_old_triple_certificate
