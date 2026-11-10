import PASoundness.PAtoCompactCleanBijectionLeft
import PASoundness.PAtoCompactCleanBijectionRight

/-! The literal bijection matrix transfers from a supplied original graph 10
to a supplied graph 6 under explicit guarded edge equivalence. This theorem
does not construct a filtered graph or prove a quotient law. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanBijection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactDiagonalBijectionRight
open PASoundness.PAtoCompactCleanBijectionLeft PASoundness.PAtoCompactCleanBijectionRight
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Both guarded clause transfers yield the exact existing bijection formula. -/
def clean_bijection : KDerivation
    (imp guardedEdges.encode (imp oldMatrix10.encode bijectionFormula.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldMatrix10.encode,guardedEdges.encode]
  have hm : Context Γ oldMatrix10.encode := Context.head _ _
  have hg : Context Γ guardedEdges.encode := .hypothesis (by simp [Γ])
  have hm' : Context Γ (both (both oldLeft.encode oldRight.encode)
      (replace 6 10 orderFormula).encode) := by
    change Context Γ oldMatrix10.encode
    exact hm
  have hb := Context.conjunctionLeft hm'
  have hl := Context.conjunctionLeft hb
  have hr := Context.conjunctionRight hb
  have hnL : Context Γ leftClause.encode := .mp hl (.mp hg (.closed left_clause))
  have hnR : Context Γ rightClause.encode := .mp hr (.mp hg (.closed right_clause))
  change Context Γ (both leftClause.encode rightClause.encode)
  exact Context.conjunctionIntro hnL hnR

theorem clean_bijection_certificate : theoremCode (certificate clean_bijection) =
    imp guardedEdges.encode (imp oldMatrix10.encode bijectionFormula.encode) :=
  certificate_correct clean_bijection

end PASoundness.PAtoCompactCleanBijection

#print axioms PASoundness.PAtoCompactCleanBijection.clean_bijection
#print axioms PASoundness.PAtoCompactCleanBijection.clean_bijection_certificate
