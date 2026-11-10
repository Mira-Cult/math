import PASoundness.PAtoCompactPartialInverseNoSpuriousClosed
import PASoundness.PAtoCompactPartialInverseBackwardOld
import PASoundness.PAtoCompactPartialInverseBackwardNew

/-! Pointwise backward coverage of an adjoined partial inverse. Every
adjunction, endpoint, successor and old-invariant hypothesis is explicit; no
witness existence, quantification or induction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseBackwardPoint
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactPartialInverseVacuitySymm
open PASoundness.PAtoCompactPartialInverseNoSpuriousClosed PASoundness.PAtoCompactPartialInverseBackwardOld
open PASoundness.PAtoCompactPartialInverseBackwardNew
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Old graph edges use the supplied old backward implication; the newly
appended pair uses the supplied endpoint edge and equality. -/
def backward_point : KDerivation
    (imp (successorCode 8 10 15) (imp oldBackward
      (imp (adjoinCode 7 11 9 14) (imp (pairFormula 11 13 12).encode
        (imp (equal 12 8) (imp (graphFormula 6 12 13).encode
          (imp (graphFormula 9 3 2).encode newBackwardRhs))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode 8 10 15
  let A := adjoinCode 7 11 9 14
  let Q := (pairFormula 11 13 12).encode
  let E := equal 12 8
  let W := (graphFormula 6 12 13).encode
  let N := (graphFormula 9 3 2).encode
  let R := both (equal 3 13) (equal 2 12)
  let Γ := [N,W,E,Q,A,oldBackward,S]
  have hn : Context Γ N := Context.head _ _
  have hw : Context Γ W := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hq : Context Γ Q := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have ho : Context Γ oldBackward := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hsplit : Context Γ (either oldGraph R) :=
    .mp hn (.mp hq (.mp ha (.closed no_spurious_edge_closed)))
  apply Context.disjunctionElim hsplit
  · have hg : Context (oldGraph :: Γ) oldGraph := Context.head _ _
    exact .mp hg (.mp (Context.under ho _) (.mp (Context.under hs _) (.closed old_backward_branch)))
  · have hr : Context (R :: Γ) R := Context.head _ _
    have h₃ : Context (R :: Γ) (equal 3 13) := Context.conjunctionLeft hr
    have h₂ : Context (R :: Γ) (equal 2 12) := Context.conjunctionRight hr
    exact .mp (Context.under hw _) (.mp (Context.under hs _)
      (.mp (Context.under he _) (.mp h₂ (.mp h₃ (.closed backward_new_branch)))))

theorem backward_point_certificate : theoremCode (certificate backward_point) =
    imp (successorCode 8 10 15) (imp oldBackward
      (imp (adjoinCode 7 11 9 14) (imp (pairFormula 11 13 12).encode
        (imp (equal 12 8) (imp (graphFormula 6 12 13).encode
          (imp (graphFormula 9 3 2).encode newBackwardRhs)))))) :=
  certificate_correct backward_point

end PASoundness.PAtoCompactPartialInverseBackwardPoint

#print axioms PASoundness.PAtoCompactPartialInverseBackwardPoint.backward_point
#print axioms PASoundness.PAtoCompactPartialInverseBackwardPoint.backward_point_certificate
