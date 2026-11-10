import PASoundness.PAtoCompactSeededSpanOutside
import PASoundness.CompactHilbertBasis

/-! Full fixed-name successor step for seeded common-source span existence, with two
actual forward-bijection clauses as object-level hypotheses. The inside case
constructs selected images and a new graph; the outside case reuses the old
graph. This does not perform the final candidate induction. -/
namespace PASoundness.PAtoCompactSeededSpanSuccessor

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactSeededSpanBase PASoundness.PAtoCompactCommonSourceSpanImages
open PASoundness.PAtoCompactSeededSpanStepWitness PASoundness.PAtoCompactSeededSpanInside
open PASoundness.PAtoCompactSeededSpanOutside PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSuccGraphOutputLift

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def fixedGuard : Formula := namedBoth firstClause
  (namedBoth secondClause (namedSuccessor 10 13 15))

def oldExists : Formula := .ex 9 seededSpan

def inductionPredicate : Formula := replace 10 30 oldExists

theorem old_instance : replace 30 10 inductionPredicate = oldExists := by decide

theorem next_instance : replace 30 13 inductionPredicate = nextExists := by decide

/-- Case split on the common input: append a pair when point 10 belongs to it,
or reuse the old graph otherwise. Both graph clauses and all source-level
membership conditions remain literal K hypotheses. -/
def successor_with_graph : KDerivation (imp fixedGuard.encode
    (imp seededSpan.encode nextExists.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [seededSpan.encode,fixedGuard.encode]
  have hi : Context Γ seededSpan.encode := .head _ _
  have hg : Context Γ fixedGuard.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ firstClause.encode := Context.conjunctionLeft hg
  have hg := Context.conjunctionRight hg
  have hs : Context Γ secondClause.encode := Context.conjunctionLeft hg
  have hsucc : Context Γ (successorCode 10 13 15) := Context.conjunctionRight hg
  have hex : Context Γ (either (member 1 10) (neg (member 1 10))) :=
    .closed (PASoundness.CompactHilbertBasis.identity (neg (member 1 10)))
  apply Context.disjunctionElim hex
  · let Δ := member 1 10 :: Γ
    have hm : Context Δ (member 1 10) := .head _ _
    have hstable : Context Δ stable.encode := Context.conjunctionIntro (.under hi _)
      (Context.conjunctionIntro hm (.under hsucc _))
    exact .mp hstable (.mp (.under hs _) (.mp (.under hf _) (.closed inside_successor)))
  · let Δ := neg (member 1 10) :: Γ
    have hm : Context Δ (neg (member 1 10)) := .head _ _
    have hout : Context Δ outsideState.encode := Context.conjunctionIntro (.under hi _)
      (Context.conjunctionIntro hm (.under hsucc _))
    have hnext : Context Δ (existsCode 9 nextInvariant.encode) :=
      .mp hout (.closed outside_graph_exists)
    simpa only [nextExists, Formula.encode] using hnext

/-- Eliminate the old graph witness. The two forward clauses and prefix
successor remain the explicit object-level guard. -/
def successor_from_graph_exists : KDerivation
    (imp fixedGuard.encode (imp oldExists.encode nextExists.encode)) := by
  have h := guarded_exists_left 9 fixedGuard.encode seededSpan.encode nextExists.encode
    (free_vacuity 9 fixedGuard (by decide)) (free_vacuity 9 nextExists (by decide))
    successor_with_graph
  simpa only [oldExists, Formula.encode] using h

/-- The same step in the actual syntactic induction predicate, from prefix 10
to its supplied successor 13. -/
def induction_successor : KDerivation (imp fixedGuard.encode
    (imp (replace 30 10 inductionPredicate).encode
      (replace 30 13 inductionPredicate).encode)) := by
  simpa only [old_instance,next_instance] using successor_from_graph_exists

theorem induction_successor_certificate : theoremCode (certificate induction_successor) =
    imp fixedGuard.encode (imp (replace 30 10 inductionPredicate).encode
      (replace 30 13 inductionPredicate).encode) := certificate_correct induction_successor

end PASoundness.PAtoCompactSeededSpanSuccessor

#print axioms PASoundness.PAtoCompactSeededSpanSuccessor.fixedGuard
#print axioms PASoundness.PAtoCompactSeededSpanSuccessor.oldExists
#print axioms PASoundness.PAtoCompactSeededSpanSuccessor.inductionPredicate
#print axioms PASoundness.PAtoCompactSeededSpanSuccessor.old_instance
#print axioms PASoundness.PAtoCompactSeededSpanSuccessor.next_instance
#print axioms PASoundness.PAtoCompactSeededSpanSuccessor.successor_with_graph
#print axioms PASoundness.PAtoCompactSeededSpanSuccessor.successor_from_graph_exists
#print axioms PASoundness.PAtoCompactSeededSpanSuccessor.induction_successor
#print axioms PASoundness.PAtoCompactSeededSpanSuccessor.induction_successor_certificate
