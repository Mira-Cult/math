import PASoundness.PAtoCompactCommonSourceSpanAppend
import PASoundness.PAtoCompactZeroSuccessor
import PASoundness.PAtoCompactSuccGraphOutputLift
import PASoundness.PAtoCompactTransitiveClosure

/-! The selected-image case of a common-source span successor step. The two
input graph edges share common witness 10, and the newly adjoined output edge
uses the same two image values. All image, membership, successor, pair and
adjunction hypotheses remain explicit K antecedents. This does not establish
old-edge preservation, the full graph invariant or induction. -/
namespace PASoundness.PAtoCompactCommonSourceSpanSelectedStep

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactCommonSourceSpanAppend
open PASoundness.PAtoCompactCommonSourceSpanBase
open PASoundness.PAtoCompactSuccGraphOutputLift PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The selected endpoints 11,12 in the successor-prefix span. Name 4 is a
single common-input witness for both original graph edges. -/
def selectedPathBody : Formula := namedBoth (.member 1 4)
  (namedBoth (.member 13 4)
    (namedBoth (graphFormula 6 4 11) (graphFormula 7 4 12)))

def selectedPath : Formula := .ex 4 selectedPathBody

def selectedAtTen : Formula := namedBoth (.member 1 10)
  (namedBoth (.member 13 10)
    (namedBoth (graphFormula 6 10 11) (graphFormula 7 10 12)))

theorem selected_substitution : replace 4 10 selectedPathBody = selectedAtTen := by decide

/-- The original span path with prefix 10 replaced by its successor 13. -/
def successorPath : Formula := replace 10 13 spanPath

def successorPathBody : Formula := namedBoth (.member 1 4)
  (namedBoth (.member 13 4)
    (namedBoth (graphFormula 6 4 2) (graphFormula 7 4 3)))

theorem successor_path_syntax : successorPath = .ex 4 successorPathBody := by decide

/-- A path through the old common-input prefix is still a path through its
successor, with the same common witness and both original graph edges. -/
def old_path_preserved : KDerivation
    (imp (successorCode 10 13 15) (imp spanPath.encode successorPath.encode)) := by
  let S := successorCode 10 13 15
  let B := spanPathBody
  have hpoint : KDerivation (imp S (imp B.encode successorPath.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [B.encode,S]
    have hb : Context Γ B.encode := .head _ _
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hc : Context Γ (member 1 4) := Context.conjunctionLeft hb
    have htail := Context.conjunctionRight hb
    have hp : Context Γ (member 10 4) := Context.conjunctionLeft htail
    have hgraphs := Context.conjunctionRight htail
    have hnew : Context Γ (member 13 4) := by
      have he : Context Γ (either (equal 4 10) (member 10 4)) :=
        Context.disjunctionRight (a := equal 4 10) hp
      exact .mp he (.mp hs (.closed (successor_include 10 13 15 4
        (by decide) (by decide) (by decide))))
    have hn : Context Γ successorPathBody.encode :=
      Context.conjunctionIntro hc (Context.conjunctionIntro hnew hgraphs)
    have hi := existsIntroduce 4 successorPathBody (by decide)
    have hr : Context Γ (existsCode 4 successorPathBody.encode) := .mp hn (.closed hi)
    simpa only [successor_path_syntax, Formula.encode] using hr
  have hvS : KDerivation (imp S (allCode 4 S)) :=
    successor_vacuity 10 13 15 4 (by decide) (by decide) (by decide)
  have hvT : KDerivation (imp successorPath.encode (allCode 4 successorPath.encode)) :=
    free_vacuity 4 successorPath (by decide)
  have h := guarded_exists_left 4 S B.encode successorPath.encode hvS hvT hpoint
  simpa only [spanPath, Formula.encode] using h

private def successorPathFirst : Formula := replace 2 11 successorPath

theorem selected_path_alignment : replace 3 12 successorPathFirst = selectedPath := by decide

/-- Transport the selected path back to arbitrary edge labels when those
labels are equal to the selected images. -/
def selected_path_to_queried : KDerivation
    (imp (equal 2 11) (imp (equal 3 12)
      (imp selectedPath.encode successorPath.encode))) := by
  have hfirst := (equalityReplace 2 11 successorPath (by decide) (by decide)).2
  have hsecond := (equalityReplace 3 12 successorPathFirst (by decide) (by decide)).2
  change KDerivation (imp (equal 2 11)
    (imp successorPathFirst.encode successorPath.encode)) at hfirst
  rw [selected_path_alignment] at hsecond
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [selectedPath.encode, equal 3 12, equal 2 11]
  have hp : Context Γ selectedPath.encode := .head _ _
  have h3 : Context Γ (equal 3 12) := .hypothesis (by simp [Γ])
  have h2 : Context Γ (equal 2 11) := .hypothesis (by simp [Γ])
  have hm : Context Γ successorPathFirst.encode := .mp hp (.mp h3 (.closed hsecond))
  exact .mp hm (.mp h2 (.closed hfirst))

/-- From the common input and both selected images, the successor prefix
contains a path using exactly that common input as witness. -/
def selected_path : KDerivation
    (imp (member 1 10)
      (imp (successorCode 10 13 15)
        (imp (graphFormula 6 10 11).encode
          (imp (graphFormula 7 10 12).encode selectedPath.encode)))) := by
  have hi := exists_variable_intro 4 10 selectedPathBody (by decide) (by decide) (by decide)
  rw [selected_substitution] at hi
  have hm := successor_contains_input 10 13 15 (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 7 10 12).encode, (graphFormula 6 10 11).encode,
    successorCode 10 13 15, member 1 10]
  have hg : Context Γ (graphFormula 7 10 12).encode := .head _ _
  have hf : Context Γ (graphFormula 6 10 11).encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 10 13 15) := .hypothesis (by simp [Γ])
  have hinput : Context Γ (member 1 10) := .hypothesis (by simp [Γ])
  have hprefix : Context Γ (member 13 10) := .mp hs (.closed hm)
  have hbody : Context Γ selectedAtTen.encode :=
    Context.conjunctionIntro hinput (Context.conjunctionIntro hprefix
      (Context.conjunctionIntro hf hg))
  simpa only [selectedPath, Formula.encode] using Context.mp hbody (.closed hi)

/-- Under the selected image edges and actual pair/graph witnesses, K derives
both the selected path and its newly adjoined output edge. -/
def selected_path_and_edge : KDerivation
    (imp (member 1 10)
      (imp (successorCode 10 13 15)
        (imp (graphFormula 6 10 11).encode
          (imp (graphFormula 7 10 12).encode
            (imp (pairFormula 16 11 12).encode
              (imp (adjoinCode 9 16 17 18)
                (both selectedPath.encode (graphFormula 17 11 12).encode))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [adjoinCode 9 16 17 18, (pairFormula 16 11 12).encode,
    (graphFormula 7 10 12).encode, (graphFormula 6 10 11).encode,
    successorCode 10 13 15, member 1 10]
  have ha : Context Γ (adjoinCode 9 16 17 18) := .head _ _
  have hp : Context Γ (pairFormula 16 11 12).encode := .hypothesis (by simp [Γ])
  have hg : Context Γ (graphFormula 7 10 12).encode := .hypothesis (by simp [Γ])
  have hf : Context Γ (graphFormula 6 10 11).encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 10 13 15) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 1 10) := .hypothesis (by simp [Γ])
  have hpath : Context Γ selectedPath.encode :=
    .mp hg (.mp hf (.mp hs (.mp hm (.closed selected_path))))
  have hedge : Context Γ (graphFormula 17 11 12).encode :=
    .mp hp (.mp ha (.closed selected_adjoined_edge))
  exact Context.conjunctionIntro hpath hedge

theorem selected_path_and_edge_certificate :
    theoremCode (certificate selected_path_and_edge) =
      imp (member 1 10)
        (imp (successorCode 10 13 15)
          (imp (graphFormula 6 10 11).encode
            (imp (graphFormula 7 10 12).encode
              (imp (pairFormula 16 11 12).encode
                (imp (adjoinCode 9 16 17 18)
                  (both selectedPath.encode (graphFormula 17 11 12).encode)))))) :=
  certificate_correct selected_path_and_edge

end PASoundness.PAtoCompactCommonSourceSpanSelectedStep

#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.selectedPathBody
#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.selectedPath
#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.selectedAtTen
#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.selected_substitution
#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.successorPath
#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.successorPathBody
#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.successor_path_syntax
#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.old_path_preserved
#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.selected_path_alignment
#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.selected_path_to_queried
#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.selected_path
#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.selected_path_and_edge
#print axioms PASoundness.PAtoCompactCommonSourceSpanSelectedStep.selected_path_and_edge_certificate
