import PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
import PASoundness.PAtoCompactMultiplicationEdgeBranchFirst
import PASoundness.PAtoCompactFreeVacuity

/-! Split an actual queried product triple into the explicit old-graph or
new-row branch using the supplied fixed-prefix no-garbage invariant. The
same outer edge witness is retained; no pair-object extensionality, graph
construction, row collection, or multiplication totality is assumed. -/
namespace PASoundness.PAtoCompactMultiplicationFirstBranchSplit
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactMultiplicationOldTripleIntro
open PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha PASoundness.PAtoCompactMultiplicationEdgeBranchFirst
open PASoundness.PAtoCompactMultiplicationRowQueryFirst PASoundness.PAtoCompactMultiplicationRowQueryFirstExists
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Literal named disjunction of the queried old triple and new-row branch. -/
def branchResult : Formula := namedEither oldTriple queriedNewRow

private def point : KDerivation (imp (noGarbage 64).encode
    (imp (namedBoth coordinates (outerBody 63)).encode branchResult.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(namedBoth coordinates (outerBody 63)).encode,(noGarbage 64).encode]
  have hb : Context Γ (both coordinates.encode (both (member 64 63)
      (PASoundness.PAtoCompactOrderIsomorphism.pairFormula 63 18 5).encode)) := by
    have h : Context Γ (namedBoth coordinates (outerBody 63)).encode := .head _ _
    simpa [outerBody,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hn : Context Γ (noGarbage 64).encode := .hypothesis (by simp [Γ])
  have hc : Context Γ coordinates.encode := Context.conjunctionLeft hb
  have hm : Context Γ (member 64 63) := Context.conjunctionLeft (Context.conjunctionRight hb)
  have hp : Context Γ (PASoundness.PAtoCompactOrderIsomorphism.pairFormula 63 18 5).encode :=
    Context.conjunctionRight (Context.conjunctionRight hb)
  have hq : Context Γ queryPairs.encode := by
    have h := Context.conjunctionIntro hp hc
    simpa [queryPairs,coordinates,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hr := Context.mp hm (Context.mp hq (Context.mp hn (.closed edge_branch)))
  simpa [branchResult,namedEither,Formula.not,Formula.encode,either,neg] using hr

private def lift_exists (x P A B : Nat)
    (hP : KDerivation (imp P (allCode x P)))
    (hB : KDerivation (imp B (allCode x B)))
    (h : KDerivation (imp P (imp A B))) : KDerivation (imp P (imp (existsCode x A) B)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hp : Context [P] P := .head _ _
  have hpstep : Context [P] (imp A B) := .mp hp (.closed h)
  have hv : ∀ z, z ∈ [P] → KDerivation (imp z (allCode x z)) := by
    intro z hz
    have he : z = P := by simpa using hz
    subst z
    exact hP
  have hall : Context [P] (allCode x (imp A B)) := Context.generalize x hv hpstep
  exact Context.existsElim hB (.under hall _) (.head _ _)

/-- The actual queried triple of graph 64 belongs to the old graph or has a
witness in the explicit new-row branch. -/
def first_branch_split : KDerivation (imp (noGarbage 64).encode
    (imp queriedTriple.encode branchResult.encode)) := by
  have hn63 := (noGarbage 64).vacuity 63 (by decide)
  have hn18 := (noGarbage 64).vacuity 18 (by decide)
  have hb63 := free_vacuity 63 branchResult (by decide)
  have hb18 := free_vacuity 18 branchResult (by decide)
  have h63 := lift_exists 63 (noGarbage 64).encode
    (namedBoth coordinates (outerBody 63)).encode branchResult.encode hn63 hb63 point
  have h18 := lift_exists 18 (noGarbage 64).encode
    (existsCode 63 (namedBoth coordinates (outerBody 63)).encode) branchResult.encode hn18 hb18 h63
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [queriedTriple.encode,(noGarbage 64).encode]
  have ht : Context Γ queriedTriple.encode := .head _ _
  have hn : Context Γ (noGarbage 64).encode := .hypothesis (by simp [Γ])
  have he := Context.mp ht (.closed triple_to_expanded)
  change Context Γ (existsCode 18 (existsCode 63 (namedBoth coordinates (outerBody 63)).encode)) at he
  exact .mp he (.mp hn (.closed h18))

theorem first_branch_split_certificate : theoremCode (certificate first_branch_split) =
    imp (noGarbage 64).encode (imp queriedTriple.encode branchResult.encode) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationFirstBranchSplit
#print axioms PASoundness.PAtoCompactMultiplicationFirstBranchSplit.first_branch_split
#print axioms PASoundness.PAtoCompactMultiplicationFirstBranchSplit.first_branch_split_certificate
