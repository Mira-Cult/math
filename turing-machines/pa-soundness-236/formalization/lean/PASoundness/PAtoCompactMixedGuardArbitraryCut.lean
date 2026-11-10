import PASoundness.PAtoCompactMixedGuardFromCandidates
import PASoundness.PAtoCompactCandidateTransitiveTests

/-! Derive a mixed guard from an exactly aligned whole candidate and a cut
candidate with arbitrary supplied binder labels. The cut's transitivity tests
are renamed explicitly inside K. Other cut and point facts remain antecedents. -/
namespace PASoundness.PAtoCompactMixedGuardArbitraryCut

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactLocalCompareChosen PASoundness.PAtoCompactAdditionGenericMixedOrder
open PASoundness.PAtoCompactAdditionMixedOrderPair PASoundness.PAtoCompactMixedGuardFromCandidates
open PASoundness.PAtoCompactCandidateTransitiveTests

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Only the whole candidate must have the chosen least-field binders here;
the cut candidate may use its own distinct transitivity labels. -/
def mixed_guard_from_cut_candidate (whole cut old new bw bc p q a k l m g : Nat)
    (fresh : [cut,p,q,firstTest whole cut old new,secondTest whole cut old new].Nodup) : KDerivation
    (imp (shapedCandidate whole whole cut old new bw)
      (imp (candidateCode cut bc p q a k l m g)
        (imp (either (equal cut whole) (member whole cut))
          (imp (member cut old) (imp (member whole new)
            (imp (neg (member cut new)) (mixedGuard whole cut old new))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let W := shapedCandidate whole whole cut old new bw
  let C := candidateCode cut bc p q a k l m g
  let R := either (equal cut whole) (member whole cut)
  let O := member cut old
  let N := member whole new
  let X := neg (member cut new)
  let Γ := [X,N,O,R,C,W]
  have hx : Context Γ X := .head _ _
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hr : Context Γ R := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hw : Context Γ W := .hypothesis (by simp [Γ])
  have hwtrans : Context Γ (transitiveCode whole (firstTest whole cut old new)
      (secondTest whole cut old new)) := Context.conjunctionLeft (Context.conjunctionLeft hw)
  have hctrans : Context Γ (transitiveCode cut (firstTest whole cut old new)
      (secondTest whole cut old new)) := .mp hc (.closed
        (candidate_transitive_tests cut bc p q a k l m g
          (firstTest whole cut old new) (secondTest whole cut old new) fresh))
  have hleast : Context Γ (chosenLeast whole old new) :=
    Context.conjunctionRight (Context.conjunctionRight hw)
  exact Context.conjunctionIntro hleast (Context.conjunctionIntro hwtrans
    (Context.conjunctionIntro hctrans (Context.conjunctionIntro hr
      (Context.conjunctionIntro ho (Context.conjunctionIntro hn hx)))))

theorem mixed_guard_from_cut_candidate_certificate (whole cut old new bw bc p q a k l m g : Nat)
    (fresh : [cut,p,q,firstTest whole cut old new,secondTest whole cut old new].Nodup) :
    theoremCode (certificate (mixed_guard_from_cut_candidate whole cut old new bw bc p q a k l m g fresh)) =
      imp (shapedCandidate whole whole cut old new bw)
        (imp (candidateCode cut bc p q a k l m g)
          (imp (either (equal cut whole) (member whole cut))
            (imp (member cut old) (imp (member whole new)
              (imp (neg (member cut new)) (mixedGuard whole cut old new)))))) :=
  certificate_correct (mixed_guard_from_cut_candidate whole cut old new bw bc p q a k l m g fresh)

end PASoundness.PAtoCompactMixedGuardArbitraryCut

#print axioms PASoundness.PAtoCompactMixedGuardArbitraryCut.mixed_guard_from_cut_candidate
#print axioms PASoundness.PAtoCompactMixedGuardArbitraryCut.mixed_guard_from_cut_candidate_certificate
