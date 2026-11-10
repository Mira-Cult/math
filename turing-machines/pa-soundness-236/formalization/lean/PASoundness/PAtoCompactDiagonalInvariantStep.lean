import PASoundness.PAtoCompactDiagonalCoverageAll
import PASoundness.PAtoCompactDiagonalNoGarbageAll
import PASoundness.PAtoCompactDiagonalGraphAlpha
import PASoundness.PAtoCompactDiagonalGraphPremises
import PASoundness.PAtoCompactDiagonalLiteralProjection
import PASoundness.PAtoCompactDiagonalAdjoinCasesAll

/-! Conditional K preservation of a diagonal graph's coverage and no-garbage
invariants by one supplied successor/point-adjunction step. The proof assumes
the successor, adjoined graph, and Kuratowski pair witness; it does not prove
unbounded graph existence, collection, induction, or a PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalInvariantStep
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactDiagonalCoverageAll
open PASoundness.PAtoCompactDiagonalNoGarbageAll PASoundness.PAtoCompactDiagonalGraphAlpha
open PASoundness.PAtoCompactDiagonalGraphPremises PASoundness.PAtoCompactDiagonalLiteralProjection
open PASoundness.PAtoCompactDiagonalAdjoinCasesAll

def oldCoverage : Nat := allCode 2 (imp (member 0 2) (graphFormula 6 2 2).encode)
def newCoverage : Nat := allCode 2 (imp (member 1 2) (graphFormula 7 2 2).encode)
def oldInvariant : Nat := both oldCoverage oldNoGarbage
def newInvariant : Nat := both newCoverage newNoGarbage

/-- The exact fixed-name K invariant step from supplied graph and pair
witnesses. The invariant contains both full coverage and no-garbage clauses. -/
def diagonal_invariant_step : KDerivation
    (imp (successorCode 0 1 2) (imp (adjoinCode 6 8 7 19)
      (imp (pairFormula 8 0 0).encode (imp oldInvariant newInvariant)))) := by
  let S := successorCode 0 1 2
  let A := adjoinCode 6 8 7 19
  let P := (pairFormula 8 0 0).encode
  let O := oldInvariant
  let Γ := [O,P,A,S]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hcov : Context Γ oldCoverage := Context.conjunctionLeft ho
  have hng : Context Γ oldNoGarbage := Context.conjunctionRight ho
  have hsc : Context Γ (allCode 2 (imp (member 1 2) (either (equal 2 0) (member 0 2)))) :=
    .mp hs (.closed successor_cases)
  have hai : Context Γ (allCode 19 (imp (member 6 19) (member 7 19))) :=
    .mp ha (.closed adjoin_inclusion)
  have hap : Context Γ (member 7 8) := .mp ha (.closed adjoin_contains_point)
  have hs4 : Context Γ (successorCode 0 1 4) := .mp hs (.closed successor_alpha)
  have ha10 : Context Γ (adjoinCode 6 8 7 10) := .mp ha (.closed adjoin_alpha)
  have hcases : Context Γ newEntryCases := .mp ha10 (.closed adjoin_cases_all)
  have hsi : Context Γ successorInclusion := .mp hs4 (.closed successor_inclusion)
  have hse : Context Γ (member 1 0) := .mp hs4 (.closed successor_endpoint)
  have hnewcov : Context Γ newCoverage :=
    .mp hp (.mp hap (.mp hcov (.mp hai (.mp hsc (.closed diagonal_coverage_all)))))
  have hnewng : Context Γ newNoGarbage :=
    .mp hp (.mp hse (.mp hsi (.mp hng (.mp hcases (.closed no_garbage_all)))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact Context.conjunctionIntro hnewcov hnewng

theorem diagonal_invariant_step_certificate :
    theoremCode (certificate diagonal_invariant_step) =
      imp (successorCode 0 1 2) (imp (adjoinCode 6 8 7 19)
        (imp (pairFormula 8 0 0).encode (imp oldInvariant newInvariant))) :=
  certificate_correct diagonal_invariant_step

end PASoundness.PAtoCompactDiagonalInvariantStep

#print axioms PASoundness.PAtoCompactDiagonalInvariantStep.diagonal_invariant_step
#print axioms PASoundness.PAtoCompactDiagonalInvariantStep.diagonal_invariant_step_certificate
