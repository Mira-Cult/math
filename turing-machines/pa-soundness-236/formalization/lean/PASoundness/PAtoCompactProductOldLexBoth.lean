import PASoundness.PAtoCompactProductOldLexSwapped

/-! Both tuple orientations of the literal old product graph's lexicographic
comparison, with all six endpoint guards and both old triple predicates kept
explicit. This does not compare outputs transported through an isomorphic cut,
establish graph extension, multiplication totality, or PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOldLexBoth
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactProductCleanLexTransfer PASoundness.PAtoCompactProductOldLexPoint
open PASoundness.PAtoCompactProductOldLexSwapped
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- From the exact old product matrix and its six endpoint memberships and
both represented triples, obtain the original and swapped comparisons. -/
def old_old_both : KDerivation (imp oldMatrixAtTen.encode
    (imp (antecedent 10).encode (both comparison.encode reverseComparison.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(antecedent 10).encode, oldMatrixAtTen.encode]
  have ha : Context Γ (antecedent 10).encode := .head _ _
  have hm : Context Γ oldMatrixAtTen.encode := .hypothesis (by simp [Γ])
  have ho : Context Γ (point 10).encode := .mp hm (.closed matrix_point_at_ten)
  have ho' : Context Γ (imp (antecedent 10).encode comparison.encode) := by
    simpa [point, Formula.encode] using ho
  have hr : Context Γ reverseComparison.encode := .mp ha (.mp hm (.closed matrix_reverse))
  exact Context.conjunctionIntro (.mp ha ho') hr

theorem old_old_both_certificate : theoremCode (certificate old_old_both) =
    imp oldMatrixAtTen.encode
      (imp (antecedent 10).encode (both comparison.encode reverseComparison.encode)) :=
  certificate_correct old_old_both
end PASoundness.PAtoCompactProductOldLexBoth
#print axioms PASoundness.PAtoCompactProductOldLexBoth.old_old_both
#print axioms PASoundness.PAtoCompactProductOldLexBoth.old_old_both_certificate
