import PASoundness.PAtoCompactDiagonalGraphSound
import PASoundness.PAtoCompactDiagonalBijection
import PASoundness.PAtoCompactDiagonalOrder
import PASoundness.PAtoCompactDiagonalInvariantStep

/-! A supplied diagonal coverage/no-garbage invariant on graph 6 yields the
exact K isomorphism matrix when the two input names are equal. This theorem
does not construct the graph or establish quotient reflexivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalIsomorphism
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactDiagonalInvariantStep
open PASoundness.PAtoCompactDiagonalNoGarbageAll PASoundness.PAtoCompactDiagonalGraphSound
open PASoundness.PAtoCompactDiagonalSoundInstance PASoundness.PAtoCompactDiagonalBijection
open PASoundness.PAtoCompactDiagonalOrder

/-- Given equal input names and both exact diagonal graph clauses, derive the
literal bijection and order matrix for graph 6. -/
def diagonal_isomorphism_matrix : KDerivation
    (imp (equal 0 1) (imp oldInvariant (both bijectionFormula.encode orderFormula.encode))) := by
  let E := equal 0 1
  let I := oldInvariant
  let Γ := [I,E]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hi : Context Γ I := Context.head _ _
  have hc : Context Γ oldCoverage := Context.conjunctionLeft hi
  have hn : Context Γ oldNoGarbage := Context.conjunctionRight hi
  have hh : Context Γ uniformEquality := .mp hn (.closed graph_equality_all)
  have hb : Context Γ bijectionFormula.encode :=
    .mp hh (.mp hc (.mp he (.closed diagonal_bijection)))
  have ho : Context Γ orderFormula.encode := .mp hh (.closed diagonal_order)
  exact Context.conjunctionIntro hb ho

theorem diagonal_isomorphism_matrix_certificate :
    theoremCode (certificate diagonal_isomorphism_matrix) =
      imp (equal 0 1) (imp oldInvariant (both bijectionFormula.encode orderFormula.encode)) :=
  certificate_correct diagonal_isomorphism_matrix

end PASoundness.PAtoCompactDiagonalIsomorphism

#print axioms PASoundness.PAtoCompactDiagonalIsomorphism.diagonal_isomorphism_matrix
#print axioms PASoundness.PAtoCompactDiagonalIsomorphism.diagonal_isomorphism_matrix_certificate
