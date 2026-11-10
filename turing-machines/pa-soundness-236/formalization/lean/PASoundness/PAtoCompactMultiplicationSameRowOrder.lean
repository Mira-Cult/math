import PASoundness.PAtoCompactMultiplicationSameRowLex
import PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder

/-! Same-row lexicographic comparison from the supplied suffix-order graph.
Major-coordinate equality, source/target memberships, and both actual graph
edges remain explicit. This does not construct the row, recover equality
from a row witness, prove the full product matrix, or use semantic soundness. -/
namespace PASoundness.PAtoCompactMultiplicationSameRowOrder
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationSameRowLex
open PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The two row points belong to the suffix graph's stated endpoints and
have the displayed graph edges. -/
def rowPoints : Nat := both (member 31 4) (both (member 31 8)
  (both (member 40 5) (both (member 40 9)
    (both (graphFormula 6 4 5).encode (graphFormula 6 8 9).encode))))

/-- The actual suffix-order clause proves both same-row lex comparisons,
given major-coordinate equality and the two explicit row points. -/
def same_row_order : KDerivation (imp suffixOrder.encode (imp (equal 3 7)
    (imp rowPoints (both forwardClause reverseClause)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [rowPoints,equal 3 7,suffixOrder.encode]
  have hp : Context Γ rowPoints := .head _ _
  have he : Context Γ (equal 3 7) := .hypothesis (by simp [Γ])
  have ho : Context Γ suffixOrder.encode := .hypothesis (by simp [Γ])
  have hm4 : Context Γ (member 31 4) := Context.conjunctionLeft hp
  have h1 := Context.conjunctionRight hp
  have hm8 : Context Γ (member 31 8) := Context.conjunctionLeft h1
  have h2 := Context.conjunctionRight h1
  have hm5 : Context Γ (member 40 5) := Context.conjunctionLeft h2
  have h3 := Context.conjunctionRight h2
  have hm9 : Context Γ (member 40 9) := Context.conjunctionLeft h3
  have h4 := Context.conjunctionRight h3
  have he45 : Context Γ (graphFormula 6 4 5).encode := Context.conjunctionLeft h4
  have he89 : Context Γ (graphFormula 6 8 9).encode := Context.conjunctionRight h4
  have hrf : Context Γ (both (member 31 8) (both (member 31 4)
      (both (member 40 9) (both (member 40 5)
        (both (graphFormula 6 8 9).encode (graphFormula 6 4 5).encode))))) :=
    Context.conjunctionIntro hm8 (Context.conjunctionIntro hm4 (Context.conjunctionIntro hm9
      (Context.conjunctionIntro hm5 (Context.conjunctionIntro he89 he45))))
  have hf : Context Γ forwardMinor := by
    simpa [rowPoints,forwardMinor] using (Context.mp hp (Context.mp ho (.closed forward_instance)))
  have hr : Context Γ reverseMinor := by
    simpa [reverseMinor] using (Context.mp hrf (Context.mp ho (.closed reverse_instance)))
  exact .mp hr (.mp hf (.mp he (.closed same_row_lex)))

theorem same_row_order_certificate : theoremCode (certificate same_row_order) =
    imp suffixOrder.encode (imp (equal 3 7) (imp rowPoints (both forwardClause reverseClause))) :=
  certificate_correct same_row_order
end PASoundness.PAtoCompactMultiplicationSameRowOrder
#print axioms PASoundness.PAtoCompactMultiplicationSameRowOrder.same_row_order
#print axioms PASoundness.PAtoCompactMultiplicationSameRowOrder.same_row_order_certificate
