import PASoundness.PAtoCompactAdditionMixedOrderPair
import PASoundness.PAtoCompactCandidateExact

/-! Derive the numerical mixed-order guard from explicitly supplied candidate
codes with the exact bound-label choices used by the local comparison. The
cut relation, actual endpoint memberships and outside-cut fact remain literal
antecedents. Aligning independently presented candidate binders is separate. -/
namespace PASoundness.PAtoCompactMixedGuardFromCandidates

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactLocalCompareChosen PASoundness.PAtoCompactLocalPairFresh PASoundness.PAtoCompactPairFilter
open PASoundness.PAtoCompactAdditionGenericMixedOrder PASoundness.PAtoCompactAdditionMixedOrderPair

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A candidate code whose transitivity and least-subset binders match the
concrete mixed-order proof's chosen names. -/
def shapedCandidate (x whole cut old new b : Nat) : Nat :=
  let t := testName whole old new
  let c := pairWitness whole t old new
  candidateCode x b (firstTest whole cut old new) (secondTest whole cut old new)
    (c+1) t (c+2) (c+3) (c+4)

/-- The two exact supplied candidate codes provide the three structural
fields of mixedGuard; the four remaining point facts are explicit inputs. -/
def mixed_guard_from_candidates (whole cut old new bw bc : Nat) : KDerivation
    (imp (shapedCandidate whole whole cut old new bw)
      (imp (shapedCandidate cut whole cut old new bc)
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
  let C := shapedCandidate cut whole cut old new bc
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
      (secondTest whole cut old new)) := Context.conjunctionLeft (Context.conjunctionLeft hc)
  have hleast : Context Γ (chosenLeast whole old new) :=
    Context.conjunctionRight (Context.conjunctionRight hw)
  exact Context.conjunctionIntro hleast (Context.conjunctionIntro hwtrans
    (Context.conjunctionIntro hctrans (Context.conjunctionIntro hr
      (Context.conjunctionIntro ho (Context.conjunctionIntro hn hx)))))

theorem mixed_guard_from_candidates_certificate (whole cut old new bw bc : Nat) :
    theoremCode (certificate (mixed_guard_from_candidates whole cut old new bw bc)) =
      imp (shapedCandidate whole whole cut old new bw)
        (imp (shapedCandidate cut whole cut old new bc)
          (imp (either (equal cut whole) (member whole cut))
            (imp (member cut old) (imp (member whole new)
              (imp (neg (member cut new)) (mixedGuard whole cut old new)))))) :=
  certificate_correct (mixed_guard_from_candidates whole cut old new bw bc)

end PASoundness.PAtoCompactMixedGuardFromCandidates

#print axioms PASoundness.PAtoCompactMixedGuardFromCandidates.shapedCandidate
#print axioms PASoundness.PAtoCompactMixedGuardFromCandidates.mixed_guard_from_candidates
#print axioms PASoundness.PAtoCompactMixedGuardFromCandidates.mixed_guard_from_candidates_certificate
