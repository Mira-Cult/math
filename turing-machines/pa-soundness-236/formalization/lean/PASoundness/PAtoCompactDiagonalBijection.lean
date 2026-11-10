import PASoundness.PAtoCompactDiagonalBijectionLeft
import PASoundness.PAtoCompactDiagonalBijectionRight

/-! The exact candidate bijection formula follows in K from equal inputs,
supplied diagonal coverage, and the supplied uniform graph-equality clause.
This does not prove these premises, construct a graph, or establish quotient
reflexivity or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalBijection
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactDiagonalSoundInstance

/-- The left and right source interfaces have exactly the same coverage code. -/
theorem coverage_alignment : PAtoCompactDiagonalBijectionLeft.coverage =
    PAtoCompactDiagonalBijectionRight.coverage := rfl

/-- The two independent descriptions of uniform soundness are literally the
same encoded formula. -/
theorem soundness_alignment : equalSoundness.encode =
    PAtoCompactDiagonalBijectionRight.uniformEquality := rfl

/-- The left clause is the first conjunct in the existing matrix syntax. -/
theorem left_alignment : PAtoCompactDiagonalBijectionLeft.leftFormula =
    PAtoCompactDiagonalBijectionRight.leftClause := rfl

/-- Assemble both checked K clauses into the exact bijection matrix. -/
def diagonal_bijection : KDerivation (imp (equal 0 1)
    (imp PAtoCompactDiagonalBijectionRight.coverage
      (imp equalSoundness.encode bijectionFormula.encode))) := by
  let E := equal 0 1
  let C := PAtoCompactDiagonalBijectionRight.coverage
  let H := equalSoundness.encode
  let Γ := [H,C,E]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hh : Context Γ H := Context.head _ _
  have hl : Context Γ PAtoCompactDiagonalBijectionLeft.leftFormula.encode :=
    .mp he (.mp hc (.mp hh (.closed PAtoCompactDiagonalBijectionLeft.left_clause)))
  have hr : Context Γ PAtoCompactDiagonalBijectionRight.rightClause.encode :=
    .mp hh (.mp hc (.mp he (.closed PAtoCompactDiagonalBijectionRight.right_clause)))
  have hl' : Context Γ PAtoCompactDiagonalBijectionRight.leftClause.encode := by
    simpa only [left_alignment] using hl
  rw [PAtoCompactDiagonalBijectionRight.bijection_alignment]
  exact Context.conjunctionIntro hl' hr

theorem diagonal_bijection_certificate : theoremCode (certificate diagonal_bijection) =
    imp (equal 0 1) (imp PAtoCompactDiagonalBijectionRight.coverage
      (imp equalSoundness.encode bijectionFormula.encode)) :=
  certificate_correct diagonal_bijection

end PASoundness.PAtoCompactDiagonalBijection

#print axioms PASoundness.PAtoCompactDiagonalBijection.diagonal_bijection
#print axioms PASoundness.PAtoCompactDiagonalBijection.diagonal_bijection_certificate
