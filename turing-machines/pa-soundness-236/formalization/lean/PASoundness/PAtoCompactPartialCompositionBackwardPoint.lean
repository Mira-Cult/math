import PASoundness.PAtoCompactCompositionNoSpurious
import PASoundness.PAtoCompactPartialCompositionBackwardOld
import PASoundness.PAtoCompactPartialCompositionBackwardNew

/-! Pointwise backward coverage for an explicitly supplied composition graph
extension. The previous invariant instance, successor, selected path, pair and
adjunction are assumptions; no graph existence or induction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionBackwardPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactCompositionNoSpurious
open PASoundness.PAtoCompactPartialCompositionBackwardOld PASoundness.PAtoCompactPartialCompositionBackwardNew
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- An edge of the supplied new graph is justified by membership in the
successor prefix and by a represented two-edge path. -/
def backward_point : KDerivation
    (imp (successorCode 10 13 15)
      (imp (imp (graphFormula 9 2 3).encode (both (member 10 2) path.encode))
        (imp adjacent (imp selected (imp (member 1 11)
          (imp (graphFormula 6 10 11).encode (imp (graphFormula 7 11 12).encode
            (imp (graphFormula 17 2 3).encode (both (member 13 2) path.encode))))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode 10 13 15
  let H := imp (graphFormula 9 2 3).encode (both (member 10 2) path.encode)
  let F := (graphFormula 6 10 11).encode
  let G := (graphFormula 7 11 12).encode
  let N := (graphFormula 17 2 3).encode
  let T := both (member 13 2) path.encode
  let Γ := [N,G,F,member 1 11,selected,adjacent,H,S]
  have hn : Context Γ N := Context.head _ _
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 11) := .hypothesis (by simp [Γ])
  have hp : Context Γ selected := .hypothesis (by simp [Γ])
  have ha : Context Γ adjacent := .hypothesis (by simp [Γ])
  have ho : Context Γ H := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hsplit : Context Γ (either (graphFormula 9 2 3).encode
      (both (equal 2 10) (equal 3 12))) :=
    .mp hn (.mp hp (.mp ha (.closed no_spurious_edge)))
  apply Context.disjunctionElim hsplit
  · have he : Context ((graphFormula 9 2 3).encode :: Γ)
        (graphFormula 9 2 3).encode := Context.head _ _
    exact .mp he (.mp (Context.under ho _) (.mp (Context.under hs _)
      (.closed (old_backward_branch path.encode))))
  · have he : Context (both (equal 2 10) (equal 3 12) :: Γ)
        (both (equal 2 10) (equal 3 12)) := Context.head _ _
    have h2 := Context.conjunctionLeft he
    have h3 := Context.conjunctionRight he
    exact .mp (Context.under hg _) (.mp (Context.under hf _) (.mp (Context.under hm _)
      (.mp (Context.under hs _) (.mp h3 (.mp h2 (.closed new_edge_backward))))))

theorem backward_point_certificate : theoremCode (certificate backward_point) =
    imp (successorCode 10 13 15)
      (imp (imp (graphFormula 9 2 3).encode (both (member 10 2) path.encode))
        (imp adjacent (imp selected (imp (member 1 11)
          (imp (graphFormula 6 10 11).encode (imp (graphFormula 7 11 12).encode
            (imp (graphFormula 17 2 3).encode (both (member 13 2) path.encode)))))))) :=
  certificate_correct backward_point

end PASoundness.PAtoCompactPartialCompositionBackwardPoint

#print axioms PASoundness.PAtoCompactPartialCompositionBackwardPoint.backward_point
#print axioms PASoundness.PAtoCompactPartialCompositionBackwardPoint.backward_point_certificate
