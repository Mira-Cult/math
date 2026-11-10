import PASoundness.PAtoCompactAdditionLeftClauseClosed
import PASoundness.PAtoCompactAdditionRightBijectionClosed

/-! The bijection clause for the unequal-top addition-successor extension.
All old-graph, filter, pair, successor and adjunction assumptions are literal
K antecedents. This neither constructs these witnesses nor proves the order
clause, isomorphism, addition totality, or the PA bridge. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionCombinedBijection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdditionOldTargetFromBijection
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def L := PAtoCompactAdditionLeftQuantified.leftClause
private def R := PAtoCompactAdditionRightBijectionCases.rightClause
/-- Literal filter, old matrix, clean graph, source successor, graph adjunction,
and appended pair. -/
def premises := PAtoCompactAdditionRightContext.premises
/-- Literal adjunction of the whole result to the old suffix. -/
def suffixAdjoin := adjoinCode 34 32 40 41
private def B := PAtoCompactAdditionOldSourceClosed.oldBijection
private def C := PAtoCompactAdditionSuccessorGraphClean.oldClean
private def Q := pairFormula 11 31 32
private def A := adjoinCode 6 11 9 16
private def S := successorCode 31 38 39

/-- The exact target bijection formula is the conjunction of the independently
constructed left and right clauses. -/
theorem bijection_alignment :
    replace 8 40 (replace 7 38 newBijection) = namedBoth L R := by decide

private theorem matrix_alignment : oldMatrixAt = namedBoth B
    (replace 1 34 (replace 0 31 orderFormula)) := by decide

/-- The full literal bijection follows under the supplied old matrix, suffix
filter and graph construction premises. No transitivity of the suffix is used. -/
def combined_bijection : KDerivation (imp premises.encode (imp suffixAdjoin
    (replace 8 40 (replace 7 38 newBijection)).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [suffixAdjoin,premises.encode]
  have ht : Context Γ suffixAdjoin := .head _ _
  have hp : Context Γ premises.encode := .hypothesis (by simp [Γ])
  have hf := Context.conjunctionLeft hp
  have hp1 := Context.conjunctionRight hp
  have hm : Context Γ oldMatrixAt.encode := Context.conjunctionLeft hp1
  have hc : Context Γ C.encode := Context.conjunctionLeft (Context.conjunctionRight hp1)
  have hp3 := Context.conjunctionRight (Context.conjunctionRight hp1)
  have hs : Context Γ S := Context.conjunctionLeft hp3
  have hp4 := Context.conjunctionRight hp3
  have ha : Context Γ A := Context.conjunctionLeft hp4
  have hq : Context Γ Q.encode := Context.conjunctionRight hp4
  have hb : Context Γ B.encode := by
    rw [matrix_alignment] at hm
    exact Context.conjunctionLeft hm
  have hlp : Context Γ PAtoCompactAdditionLeftPremises.premisesCode := by
    change Context Γ (both B.encode (both C.encode (both A (both Q.encode (both suffixAdjoin S)))))
    exact Context.conjunctionIntro hb (Context.conjunctionIntro hc (Context.conjunctionIntro ha
      (Context.conjunctionIntro hq (Context.conjunctionIntro ht hs))))
  have hl : Context Γ L.encode := .mp hlp (.closed PAtoCompactAdditionLeftClauseClosed.left_clause_closed)
  have hr : Context Γ R.encode := .mp ht (.mp hp (.closed PAtoCompactAdditionRightBijectionClosed.right_bijection_closed))
  rw [bijection_alignment]
  exact Context.conjunctionIntro hl hr

theorem combined_bijection_certificate : theoremCode (certificate combined_bijection) =
    imp premises.encode (imp suffixAdjoin (replace 8 40 (replace 7 38 newBijection)).encode) :=
  certificate_correct combined_bijection
end PASoundness.PAtoCompactAdditionCombinedBijection
#print axioms PASoundness.PAtoCompactAdditionCombinedBijection.bijection_alignment
#print axioms PASoundness.PAtoCompactAdditionCombinedBijection.combined_bijection
#print axioms PASoundness.PAtoCompactAdditionCombinedBijection.combined_bijection_certificate
