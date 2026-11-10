import PASoundness.PAtoCompactSeededSpanInside
import PASoundness.PAtoCompactCommonSourceSpanOutside

/-! Outside-source successor for seeded span collection. A new prefix point
outside the common input creates no new path; the same graph and original
seed disjunct remain a valid witness. Candidate induction is not proved here. -/
namespace PASoundness.PAtoCompactSeededSpanOutside

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSeededSpanBase PASoundness.PAtoCompactSeededSpanStepWitness
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactCommonSourceSpanSelectedStep
open PASoundness.PAtoCompactCommonSourceSpanOutside (outsideGuard new_path_was_old)

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def outsideState : Formula := namedBoth seededSpan outsideGuard

private def oldPoint : Formula := .imp (namedBoth (.member 0 2) (.member 8 3))
  (namedBoth (.imp (graphFormula 9 2 3) (namedEither (graphFormula 14 2 3) spanPath))
    (.imp (namedEither (graphFormula 14 2 3) spanPath) (graphFormula 9 2 3)))

private def newPoint : Formula := .imp (namedBoth (.member 0 2) (.member 8 3))
  (namedBoth (.imp (graphFormula 9 2 3) (namedEither (graphFormula 14 2 3) successorPath))
    (.imp (namedEither (graphFormula 14 2 3) successorPath) (graphFormula 9 2 3)))

private theorem old_syntax : seededSpan = .all 2 (.all 3 oldPoint) := rfl
private theorem new_syntax : nextInvariant = .all 2 (.all 3 newPoint) := by decide

private def old_specialize : KDerivation (imp seededSpan.encode oldPoint.encode) := by
  have h2 := allSpecialize 2 (.all 3 oldPoint) (by decide)
  have h3 := allSpecialize 3 oldPoint (by decide)
  have h := compose h2 h3
  simpa only [old_syntax, Formula.encode] using h

/-- The original graph still satisfies the seeded invariant after adding a
prefix point outside the common input. -/
def outside_next_invariant : KDerivation (imp outsideState.encode nextInvariant.encode) := by
  let Γ := [outsideState.encode]
  have hg : Context Γ outsideState.encode := .head _ _
  have hi : Context Γ seededSpan.encode := Context.conjunctionLeft hg
  have ho : Context Γ outsideGuard.encode := Context.conjunctionRight hg
  have hs : Context Γ (successorCode 10 13 15) := Context.conjunctionRight ho
  have hpoint : Context Γ newPoint.encode := by
    apply Context.deduction
    let D := both (member 0 2) (member 8 3)
    let G := (graphFormula 9 2 3).encode
    let F := (graphFormula 14 2 3).encode
    let Δ := [D,outsideState.encode]
    have hd : Context Δ D := .head _ _
    have hp : Context Δ oldPoint.encode := .mp (.under hi _) (.closed old_specialize)
    have hc : Context Δ (both (imp G (either F spanPath.encode))
        (imp (either F spanPath.encode) G)) := .mp hd hp
    have hforward : Context Δ (imp G (either F successorPath.encode)) := by
      apply Context.deduction
      let Θ := G :: Δ
      have he : Context Θ G := .head _ _
      have hcase : Context Θ (either F spanPath.encode) := .mp he (Context.conjunctionLeft (.under hc _))
      apply Context.disjunctionElim hcase
      · exact Context.disjunctionLeft (b := successorPath.encode) (.head _ _)
      · let Ξ := spanPath.encode :: Θ
        have hpath : Context Ξ spanPath.encode := .head _ _
        have hn : Context Ξ successorPath.encode :=
          .mp hpath (.mp (.under (.under (.under hs _) _) _) (.closed old_path_preserved))
        exact Context.disjunctionRight (a := F) hn
    have hbackward : Context Δ (imp (either F successorPath.encode) G) := by
      apply Context.deduction
      let Θ := either F successorPath.encode :: Δ
      have hcase : Context Θ (either F successorPath.encode) := .head _ _
      apply Context.disjunctionElim hcase
      · let Ξ := F :: Θ
        have he : Context Ξ F := .head _ _
        have hallowed : Context Ξ (either F spanPath.encode) := Context.disjunctionLeft he
        exact .mp hallowed (Context.conjunctionRight (.under (.under hc _) _))
      · let Ξ := successorPath.encode :: Θ
        have hn : Context Ξ successorPath.encode := .head _ _
        have hold : Context Ξ spanPath.encode :=
          .mp hn (.mp (.under (.under (.under ho _) _) _) (.closed new_path_was_old))
        have hallowed : Context Ξ (either F spanPath.encode) := Context.disjunctionRight hold
        exact .mp hallowed (Context.conjunctionRight (.under (.under hc _) _))
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

/-- The original graph is an actual witness for the next-prefix invariant. -/
def outside_graph_exists : KDerivation
    (imp outsideState.encode (existsCode 9 nextInvariant.encode)) :=
  compose outside_next_invariant (existsIntroduce 9 nextInvariant (by decide))

theorem outside_graph_exists_certificate : theoremCode (certificate outside_graph_exists) =
    imp outsideState.encode (existsCode 9 nextInvariant.encode) := certificate_correct outside_graph_exists

end PASoundness.PAtoCompactSeededSpanOutside

#print axioms PASoundness.PAtoCompactSeededSpanOutside.outsideState
#print axioms PASoundness.PAtoCompactSeededSpanOutside.outside_next_invariant
#print axioms PASoundness.PAtoCompactSeededSpanOutside.outside_graph_exists
#print axioms PASoundness.PAtoCompactSeededSpanOutside.outside_graph_exists_certificate
