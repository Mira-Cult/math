import PASoundness.PAtoCompactMultiplicationFourCaseLex
import PASoundness.PAtoCompactMultiplicationTwoNewRowOrder

/-! The new/new branch of the multiplication lexicographic point proof.
The common premise and its finite K projections to a clean ordered suffix
map are explicit proof inputs. This does not construct those premises, the
row graph, the other branches, or multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationNewNewCase
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactMultiplicationFourCaseLex
open PASoundness.PAtoCompactMultiplicationTwoNewRowOrder
open PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
attribute [local irreducible] imp PASoundness.Cantor.pair PASoundness.Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- A common premise with supplied K projections to the ordered clean suffix
map proves the new/new branch. The two actual row-branch witnesses remain
explicit K antecedents. -/
def new_new_from_projections (P : Nat)
    (order : KDerivation (imp P suffixOrder.encode))
    (clean : KDerivation (imp P suffixClean.encode)) :
    KDerivation (imp P (imp newFirst (imp newSecond comparisons))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [newSecond,newFirst,P]
  have h2 : Context Γ newSecond := .head _ _
  have h1 : Context Γ newFirst := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have ho : Context Γ suffixOrder.encode := .mp hp (.closed order)
  have hc : Context Γ suffixClean.encode := .mp hp (.closed clean)
  exact .mp h2 (.mp h1 (.mp hc (.mp ho (.closed two_new_row_order))))

theorem new_new_from_projections_certificate (P : Nat)
    (order : KDerivation (imp P suffixOrder.encode))
    (clean : KDerivation (imp P suffixClean.encode)) :
    theoremCode (certificate (new_new_from_projections P order clean)) =
      imp P (imp newFirst (imp newSecond comparisons)) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationNewNewCase
#print axioms PASoundness.PAtoCompactMultiplicationNewNewCase.new_new_from_projections
#print axioms PASoundness.PAtoCompactMultiplicationNewNewCase.new_new_from_projections_certificate
