import PASoundness.PAtoCompactCommonSourceSpanForward
import PASoundness.PAtoCompactCommonSourceSpanImages
import PASoundness.PAtoCompactSuccessorInjective
import PASoundness.PAtoCompactCompositionAdjoinEdges

/-! Pointwise reverse preservation for a common-source span successor. The
selected image witnesses retain their graph edges and uniqueness clauses. An
old common-source witness uses the old span invariant, while the new common
point uses image uniqueness and the adjoined edge. This does not yet assemble
the quantified invariant, eliminate graph/image witnesses, or prove induction. -/
namespace PASoundness.PAtoCompactCommonSourceSpanBackward

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactSuccessorInjective PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSuccGraphOutputLift PASoundness.PAtoCompactCommonSourceSpanBase
open PASoundness.PAtoCompactCommonSourceSpanImages PASoundness.PAtoCompactCommonSourceSpanAppend
open PASoundness.PAtoCompactCommonSourceSpanSelectedStep PASoundness.PAtoCompactCompositionAdjoinEdges

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- All retained object-level hypotheses for the fixed queried endpoints.
Both image bodies contain their actual membership, edge and uniqueness data. -/
def reverseGuard : Formula := namedBoth spanComposition
  (namedBoth firstImageBody (namedBoth secondImageBody
    (namedBoth (namedSuccessor 10 13 15)
      (namedBoth (.member 0 2) (namedBoth (.member 8 3)
        (namedBoth (pairFormula 16 11 12) (namedAdjoin 9 16 17 18)))))))

private def point : Formula := .imp (namedBoth (.member 0 2) (.member 8 3))
  (namedBoth (.imp (graphFormula 9 2 3) spanPath)
    (.imp spanPath (graphFormula 9 2 3)))

private def specialize_span : KDerivation (imp spanComposition.encode point.encode) := by
  have h2 := allSpecialize 2 (.all 3 point) (by decide)
  have h3 := allSpecialize 3 point (by decide)
  have h := compose h2 h3
  simpa only [spanComposition, point, Formula.encode] using h

private def selectedEdge := graphFormula 17 11 12
private def firstRenamed := graphFormula 17 11 3
private def queriedEdge := graphFormula 17 2 3

/-- Transport the newly selected edge to equal queried endpoint names. -/
def selected_edge_to_queried : KDerivation (imp (equal 2 11)
    (imp (equal 3 12) (imp selectedEdge.encode queriedEdge.encode))) := by
  have hfirst := (equalityReplace 2 11 queriedEdge (by decide) (by decide)).2
  have hsecond := (equalityReplace 3 12 firstRenamed (by decide) (by decide)).2
  have hs1 : replace 2 11 queriedEdge = firstRenamed := by decide
  have hs2 : replace 3 12 firstRenamed = selectedEdge := by decide
  rw [hs1] at hfirst
  rw [hs2] at hsecond
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [selectedEdge.encode,equal 3 12,equal 2 11]
  have he : Context Γ selectedEdge.encode := .head _ _
  have h3 : Context Γ (equal 3 12) := .hypothesis (by simp [Γ])
  have h2 : Context Γ (equal 2 11) := .hypothesis (by simp [Γ])
  have hm : Context Γ firstRenamed.encode := .mp he (.mp h3 (.closed hsecond))
  exact .mp hm (.mp h2 (.closed hfirst))

private def firstUniqueBody : Formula := .imp
  (namedBoth (.member 0 4) (graphFormula 6 10 4)) (.equal 4 11)
private def secondUniqueBody : Formula := .imp
  (namedBoth (.member 8 4) (graphFormula 7 10 4)) (.equal 4 12)

private def first_unique_at_two : KDerivation (imp (allCode 4 firstUniqueBody.encode)
    (imp (both (member 0 2) (graphFormula 6 10 2).encode) (equal 2 11))) := by
  have hi := universalInstance 4 2 firstUniqueBody (by decide) (by decide) (by decide)
  have hs : replace 4 2 firstUniqueBody = .imp
      (namedBoth (.member 0 2) (graphFormula 6 10 2)) (.equal 2 11) := by decide
  rw [hs] at hi
  simpa [firstUniqueBody, namedBoth, Formula.not, Formula.encode, both, neg] using hi

private def second_unique_at_three : KDerivation (imp (allCode 4 secondUniqueBody.encode)
    (imp (both (member 8 3) (graphFormula 7 10 3).encode) (equal 3 12))) := by
  have hi := universalInstance 4 3 secondUniqueBody (by decide) (by decide) (by decide)
  have hs : replace 4 3 secondUniqueBody = .imp
      (namedBoth (.member 8 3) (graphFormula 7 10 3)) (.equal 3 12) := by decide
  rw [hs] at hi
  simpa [secondUniqueBody, namedBoth, Formula.not, Formula.encode, both, neg] using hi

/-- The successor-prefix path body produces an edge in the new graph. -/
def backward_body : KDerivation
    (imp reverseGuard.encode (imp successorPathBody.encode (graphFormula 17 2 3).encode)) := by
  have hfirst := (equalityReplace 4 10 (graphFormula 6 4 2) (by decide) (by decide)).1
  have hsecond := (equalityReplace 4 10 (graphFormula 7 4 3) (by decide) (by decide)).1
  have hs1 : replace 4 10 (graphFormula 6 4 2) = graphFormula 6 10 2 := by decide
  have hs2 : replace 4 10 (graphFormula 7 4 3) = graphFormula 7 10 3 := by decide
  rw [hs1] at hfirst
  rw [hs2] at hsecond
  have hex := existsIntroduce 4 spanPathBody (by decide)
  have hinspect := successor_inspect 10 13 15 4 (by decide) (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [successorPathBody.encode, reverseGuard.encode]
  have hb : Context Γ successorPathBody.encode := .head _ _
  have hg : Context Γ reverseGuard.encode := .hypothesis (by simp [Γ])
  have hcommon := Context.conjunctionLeft hb
  have htail := Context.conjunctionRight hb
  have hprefix := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have hf := Context.conjunctionLeft htail
  have hs := Context.conjunctionRight htail
  have hinv : Context Γ spanComposition.encode := Context.conjunctionLeft hg
  have hg := Context.conjunctionRight hg
  have hfirstImage : Context Γ firstImageBody.encode := Context.conjunctionLeft hg
  have hg := Context.conjunctionRight hg
  have hsecondImage : Context Γ secondImageBody.encode := Context.conjunctionLeft hg
  have hg := Context.conjunctionRight hg
  have hsucc : Context Γ (successorCode 10 13 15) := Context.conjunctionLeft hg
  have hg := Context.conjunctionRight hg
  have hx : Context Γ (member 0 2) := Context.conjunctionLeft hg
  have hg := Context.conjunctionRight hg
  have hy : Context Γ (member 8 3) := Context.conjunctionLeft hg
  have hg := Context.conjunctionRight hg
  have hp : Context Γ (pairFormula 16 11 12).encode := Context.conjunctionLeft hg
  have ha : Context Γ (adjoinCode 9 16 17 18) := Context.conjunctionRight hg
  have hcases : Context Γ (either (equal 4 10) (member 10 4)) :=
    .mp hprefix (.mp hsucc (.closed hinspect))
  apply Context.disjunctionElim hcases
  · let Δ := equal 4 10 :: Γ
    have he : Context Δ (equal 4 10) := .head _ _
    have hf' : Context Δ (graphFormula 6 10 2).encode :=
      .mp (.under hf _) (.mp he (.closed hfirst))
    have hs' : Context Δ (graphFormula 7 10 3).encode :=
      .mp (.under hs _) (.mp he (.closed hsecond))
    have hu1 : Context Δ (allCode 4 firstUniqueBody.encode) := by
      have h : Context Δ firstImageBody.encode := Context.under hfirstImage (equal 4 10)
      change Context Δ (both (member 0 11) (both (graphFormula 6 10 11).encode
        (allCode 4 firstUniqueBody.encode))) at h
      exact Context.conjunctionRight (Context.conjunctionRight h)
    have hu2 : Context Δ (allCode 4 secondUniqueBody.encode) := by
      have h : Context Δ secondImageBody.encode := Context.under hsecondImage (equal 4 10)
      change Context Δ (both (member 8 12) (both (graphFormula 7 10 12).encode
        (allCode 4 secondUniqueBody.encode))) at h
      exact Context.conjunctionRight (Context.conjunctionRight h)
    have he1 : Context Δ (equal 2 11) := .mp
      (Context.conjunctionIntro (.under hx _) hf') (.mp hu1 (.closed first_unique_at_two))
    have he2 : Context Δ (equal 3 12) := .mp
      (Context.conjunctionIntro (.under hy _) hs') (.mp hu2 (.closed second_unique_at_three))
    have hnew : Context Δ (graphFormula 17 11 12).encode :=
      .mp (.under hp _) (.mp (.under ha _) (.closed selected_adjoined_edge))
    exact .mp hnew (.mp he2 (.mp he1 (.closed selected_edge_to_queried)))
  · let Δ := member 10 4 :: Γ
    have hm : Context Δ (member 10 4) := .head _ _
    have hbody : Context Δ spanPathBody.encode :=
      Context.conjunctionIntro (.under hcommon _) (Context.conjunctionIntro hm
        (Context.conjunctionIntro (.under hf _) (.under hs _)))
    have hpath : Context Δ spanPath.encode := by
      simpa only [spanPath, Formula.encode] using Context.mp hbody (.closed hex)
    have hpoint : Context Δ point.encode := .mp (.under hinv _) (.closed specialize_span)
    have hguard : Context Δ (both (member 0 2) (member 8 3)) :=
      Context.conjunctionIntro (.under hx _) (.under hy _)
    have hboth : Context Δ (both (imp (graphFormula 9 2 3).encode spanPath.encode)
        (imp spanPath.encode (graphFormula 9 2 3).encode)) := .mp hguard hpoint
    have hold : Context Δ (graphFormula 9 2 3).encode := .mp hpath (Context.conjunctionRight hboth)
    exact .mp hold (.mp (.under ha _) (.closed adjoin_preserves_edge))

/-- Eliminate the successor path's common-source witness, retaining the
explicit old invariant, selected image bodies, successor and graph inputs. -/
def backward_point : KDerivation
    (imp reverseGuard.encode (imp successorPath.encode (graphFormula 17 2 3).encode)) := by
  have hvG := free_vacuity 4 reverseGuard (by decide)
  have hvT := free_vacuity 4 (graphFormula 17 2 3) (by decide)
  have h := guarded_exists_left 4 reverseGuard.encode successorPathBody.encode
    (graphFormula 17 2 3).encode hvG hvT backward_body
  simpa only [successor_path_syntax, Formula.encode] using h

theorem backward_point_certificate : theoremCode (certificate backward_point) =
    imp reverseGuard.encode (imp successorPath.encode (graphFormula 17 2 3).encode) :=
  certificate_correct backward_point

end PASoundness.PAtoCompactCommonSourceSpanBackward

#print axioms PASoundness.PAtoCompactCommonSourceSpanBackward.reverseGuard
#print axioms PASoundness.PAtoCompactCommonSourceSpanBackward.selected_edge_to_queried
#print axioms PASoundness.PAtoCompactCommonSourceSpanBackward.backward_body
#print axioms PASoundness.PAtoCompactCommonSourceSpanBackward.backward_point
#print axioms PASoundness.PAtoCompactCommonSourceSpanBackward.backward_point_certificate
