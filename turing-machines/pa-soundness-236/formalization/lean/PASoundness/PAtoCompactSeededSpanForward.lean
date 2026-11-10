import PASoundness.PAtoCompactSeededSpanBase
import PASoundness.PAtoCompactCommonSourceSpanSelectedStep
import PASoundness.PAtoCompactCommonSourceSpanEdgeSplit

/-! Pointwise forward direction for adjoining one common-source pair to a
seeded span graph. Existing seed edges and previous span paths remain allowed;
the new pair introduces only its selected common-source path. No image object
or seed graph is assumed candidate. Reverse coverage and induction remain open. -/
namespace PASoundness.PAtoCompactSeededSpanForward

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCommonSourceSpanBase
open PASoundness.PAtoCompactSeededSpanBase PASoundness.PAtoCompactCommonSourceSpanSelectedStep
open PASoundness.PAtoCompactCommonSourceSpanEdgeSplit

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def point : Formula := .imp (namedBoth (.member 0 2) (.member 8 3))
  (namedBoth
    (.imp (graphFormula 9 2 3) (namedEither (graphFormula 14 2 3) spanPath))
    (.imp (namedEither (graphFormula 14 2 3) spanPath) (graphFormula 9 2 3)))

private theorem seeded_point_syntax : seededSpan = .all 2 (.all 3 point) := rfl

private def seeded_specialize : KDerivation (imp seededSpan.encode point.encode) := by
  have h2 := allSpecialize 2 (.all 3 point) (by decide)
  have h3 := allSpecialize 3 point (by decide)
  have h := compose h2 h3
  simpa only [seeded_point_syntax, Formula.encode] using h

/-- Under the old seeded invariant and the actual selected witnesses, every
edge of the new graph is a seed edge or a successor-prefix path. -/
def forward_point : KDerivation
    (imp seededSpan.encode
      (imp (member 0 2) (imp (member 8 3)
        (imp (member 1 10) (imp (successorCode 10 13 15)
          (imp (graphFormula 6 10 11).encode
            (imp (graphFormula 7 10 12).encode
              (imp (pairFormula 16 11 12).encode
                (imp (adjoinCode 9 16 17 18)
                  (imp (graphFormula 17 2 3).encode
                    (either (graphFormula 14 2 3).encode successorPath.encode))))))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Q := (graphFormula 17 2 3).encode
  let A := adjoinCode 9 16 17 18
  let P := (pairFormula 16 11 12).encode
  let E2 := (graphFormula 7 10 12).encode
  let E1 := (graphFormula 6 10 11).encode
  let S := successorCode 10 13 15
  let M := member 1 10
  let Y := member 8 3
  let X := member 0 2
  let I := seededSpan.encode
  let Seed := (graphFormula 14 2 3).encode
  let Γ := [Q,A,P,E2,E1,S,M,Y,X,I]
  have hq : Context Γ Q := .head _ _
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have he2 : Context Γ E2 := .hypothesis (by simp [Γ])
  have he1 : Context Γ E1 := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have hy : Context Γ Y := .hypothesis (by simp [Γ])
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hinv : Context Γ I := .hypothesis (by simp [Γ])
  have hsplit : Context Γ edgeConclusion.encode :=
    .mp hq (.mp hp (.mp ha (.closed adjoined_edge_split)))
  change Context Γ (either (graphFormula 9 2 3).encode
    (both (equal 2 11) (equal 3 12))) at hsplit
  apply Context.disjunctionElim hsplit
  · let Δ := (graphFormula 9 2 3).encode :: Γ
    have hold : Context Δ (graphFormula 9 2 3).encode := .head _ _
    have hpoint : Context Δ point.encode := .mp (.under hinv _) (.closed seeded_specialize)
    have hguard : Context Δ (both (member 0 2) (member 8 3)) :=
      Context.conjunctionIntro (.under hx _) (.under hy _)
    have hboth : Context Δ (both
        (imp (graphFormula 9 2 3).encode (either Seed spanPath.encode))
        (imp (either Seed spanPath.encode) (graphFormula 9 2 3).encode)) := .mp hguard hpoint
    have hcase : Context Δ (either Seed spanPath.encode) := .mp hold (Context.conjunctionLeft hboth)
    apply Context.disjunctionElim hcase
    · exact Context.disjunctionLeft (b := successorPath.encode) (.head _ _)
    · have hpath : Context (spanPath.encode :: Δ) spanPath.encode := .head _ _
      have hnew : Context (spanPath.encode :: Δ) successorPath.encode :=
        .mp hpath (.mp (.under (.under hs _) _) (.closed old_path_preserved))
      exact Context.disjunctionRight (a := Seed) hnew
  · let R := both (equal 2 11) (equal 3 12)
    let Δ := R :: Γ
    have heq : Context Δ R := .head _ _
    have hselected : Context Δ selectedPath.encode :=
      .mp (.under he2 _) (.mp (.under he1 _) (.mp (.under hs _) (.mp (.under hm _) (.closed selected_path))))
    have hnew : Context Δ successorPath.encode := .mp hselected (.mp (Context.conjunctionRight heq)
      (.mp (Context.conjunctionLeft heq) (.closed selected_path_to_queried)))
    exact Context.disjunctionRight (a := Seed) hnew

theorem forward_point_certificate : theoremCode (certificate forward_point) =
    imp seededSpan.encode
      (imp (member 0 2) (imp (member 8 3)
        (imp (member 1 10) (imp (successorCode 10 13 15)
          (imp (graphFormula 6 10 11).encode
            (imp (graphFormula 7 10 12).encode
              (imp (pairFormula 16 11 12).encode
                (imp (adjoinCode 9 16 17 18)
                  (imp (graphFormula 17 2 3).encode
                    (either (graphFormula 14 2 3).encode successorPath.encode)))))))))) :=
  certificate_correct forward_point

end PASoundness.PAtoCompactSeededSpanForward

#print axioms PASoundness.PAtoCompactSeededSpanForward.forward_point
#print axioms PASoundness.PAtoCompactSeededSpanForward.forward_point_certificate
