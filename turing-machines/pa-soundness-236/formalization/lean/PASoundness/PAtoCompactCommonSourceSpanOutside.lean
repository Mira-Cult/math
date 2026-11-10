import PASoundness.PAtoCompactCommonSourceSpanInside
import PASoundness.PAtoCompactSuccessorInjective

/-! Outside-source successor for common-source span collection. If the new
prefix point is outside the common input, no new span path is introduced, so
the old represented graph remains a witness. This does not establish the
inside-source branch, eliminate the old graph, or prove candidate induction. -/
namespace PASoundness.PAtoCompactCommonSourceSpanOutside

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactCommonSourceSpanSelectedStep
open PASoundness.PAtoCompactCommonSourceSpanStepWitness

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def outsideGuard : Formula := namedBoth (Formula.member 1 10).not (namedSuccessor 10 13 15)

def outsideState : Formula := namedBoth spanComposition outsideGuard

/-- Under the outside-source hypothesis, any path through the new prefix
already has a witness in the old prefix. -/
def new_path_was_old : KDerivation
    (imp outsideGuard.encode (imp successorPath.encode spanPath.encode)) := by
  have hpoint : KDerivation (imp outsideGuard.encode
      (imp successorPathBody.encode spanPath.encode)) := by
    have hex := existsIntroduce 4 spanPathBody (by decide)
    have hinspect := successor_inspect 10 13 15 4 (by decide) (by decide) (by decide)
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [successorPathBody.encode,outsideGuard.encode]
    have hb : Context Γ successorPathBody.encode := .head _ _
    have hg : Context Γ outsideGuard.encode := .hypothesis (by simp [Γ])
    have hnot : Context Γ (neg (member 1 10)) := Context.conjunctionLeft hg
    have hs : Context Γ (successorCode 10 13 15) := Context.conjunctionRight hg
    have hm : Context Γ (member 1 4) := Context.conjunctionLeft hb
    have htail := Context.conjunctionRight hb
    have hprefix : Context Γ (member 13 4) := Context.conjunctionLeft htail
    have hgraphs := Context.conjunctionRight htail
    have hcases : Context Γ (either (equal 4 10) (member 10 4)) :=
      .mp hprefix (.mp hs (.closed hinspect))
    apply Context.disjunctionElim hcases
    · let Δ := equal 4 10 :: Γ
      have he : Context Δ (equal 4 10) := .head _ _
      have hbad : Context Δ (member 1 10) := .mp he (.mp (.under hm _) (.closed (memberRightEquality 1 4 10)))
      exact Context.explode _ (.mp hbad (.under hnot _))
    · let Δ := member 10 4 :: Γ
      have hold : Context Δ (member 10 4) := .head _ _
      have hbody : Context Δ spanPathBody.encode :=
        Context.conjunctionIntro (.under hm _) (Context.conjunctionIntro hold (.under hgraphs _))
      simpa only [spanPath, Formula.encode] using Context.mp hbody (.closed hex)
  have h := guarded_exists_left 4 outsideGuard.encode successorPathBody.encode spanPath.encode
    (free_vacuity 4 outsideGuard (by decide)) (free_vacuity 4 spanPath (by decide)) hpoint
  simpa only [successor_path_syntax, Formula.encode] using h

private def oldPoint : Formula := .imp (namedBoth (.member 0 2) (.member 8 3))
  (namedBoth (.imp (graphFormula 9 2 3) spanPath)
    (.imp spanPath (graphFormula 9 2 3)))

private def newPoint : Formula := .imp (namedBoth (.member 0 2) (.member 8 3))
  (namedBoth (.imp (graphFormula 9 2 3) successorPath)
    (.imp successorPath (graphFormula 9 2 3)))

private theorem old_syntax : spanComposition = .all 2 (.all 3 oldPoint) := rfl
private theorem new_syntax : nextInvariant = .all 2 (.all 3 newPoint) := by decide

private def old_specialize : KDerivation (imp spanComposition.encode oldPoint.encode) := by
  have h2 := allSpecialize 2 (.all 3 oldPoint) (by decide)
  have h3 := allSpecialize 3 oldPoint (by decide)
  have h := compose h2 h3
  simpa only [old_syntax, Formula.encode] using h

/-- The existing graph satisfies the next-prefix invariant, conditional on
its old invariant, the actual prefix successor and outside membership. -/
def outside_next_invariant : KDerivation (imp outsideState.encode nextInvariant.encode) := by
  let Γ := [outsideState.encode]
  have hg : Context Γ outsideState.encode := .head _ _
  have hi : Context Γ spanComposition.encode := Context.conjunctionLeft hg
  have ho : Context Γ outsideGuard.encode := Context.conjunctionRight hg
  have hs : Context Γ (successorCode 10 13 15) := Context.conjunctionRight ho
  have hpoint : Context Γ newPoint.encode := by
    apply Context.deduction
    let D := both (member 0 2) (member 8 3)
    let Δ := [D,outsideState.encode]
    have hd : Context Δ D := .head _ _
    have hp : Context Δ oldPoint.encode := .mp (.under hi _) (.closed old_specialize)
    have hc : Context Δ (both (imp (graphFormula 9 2 3).encode spanPath.encode)
        (imp spanPath.encode (graphFormula 9 2 3).encode)) := .mp hd hp
    have hforward : Context Δ (imp (graphFormula 9 2 3).encode successorPath.encode) := by
      apply Context.deduction
      let Θ := (graphFormula 9 2 3).encode :: Δ
      have he : Context Θ (graphFormula 9 2 3).encode := .head _ _
      have hpath : Context Θ spanPath.encode := .mp he (Context.conjunctionLeft (.under hc _))
      exact .mp hpath (.mp (.under (.under hs _) _) (.closed old_path_preserved))
    have hbackward : Context Δ (imp successorPath.encode (graphFormula 9 2 3).encode) := by
      apply Context.deduction
      let Θ := successorPath.encode :: Δ
      have hn : Context Θ successorPath.encode := .head _ _
      have hpath : Context Θ spanPath.encode :=
        .mp hn (.mp (.under (.under ho _) _) (.closed new_path_was_old))
      exact .mp hpath (Context.conjunctionRight (.under hc _))
    exact Context.conjunctionIntro hforward hbackward
  have hv3 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    have he : h = outsideState.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 3 outsideState (by decide)
  have hv2 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = outsideState.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 2 outsideState (by decide)
  have hall : Context Γ nextInvariant.encode := by
    simpa only [new_syntax, Formula.encode] using
      Context.generalize 2 hv2 (Context.generalize 3 hv3 hpoint)
  exact Context.closeEmpty (Context.deduction hall)

/-- The old graph is an actual witness to the next invariant. -/
def outside_graph_exists : KDerivation
    (imp outsideState.encode (existsCode 9 nextInvariant.encode)) :=
  compose outside_next_invariant (existsIntroduce 9 nextInvariant (by decide))

theorem outside_graph_exists_certificate : theoremCode (certificate outside_graph_exists) =
    imp outsideState.encode (existsCode 9 nextInvariant.encode) :=
  certificate_correct outside_graph_exists

end PASoundness.PAtoCompactCommonSourceSpanOutside

#print axioms PASoundness.PAtoCompactCommonSourceSpanOutside.outsideGuard
#print axioms PASoundness.PAtoCompactCommonSourceSpanOutside.outsideState
#print axioms PASoundness.PAtoCompactCommonSourceSpanOutside.new_path_was_old
#print axioms PASoundness.PAtoCompactCommonSourceSpanOutside.outside_next_invariant
#print axioms PASoundness.PAtoCompactCommonSourceSpanOutside.outside_graph_exists
#print axioms PASoundness.PAtoCompactCommonSourceSpanOutside.outside_graph_exists_certificate
