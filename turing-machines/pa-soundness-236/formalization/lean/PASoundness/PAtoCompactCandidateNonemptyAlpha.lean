import PASoundness.PAtoCompactCandidateExact
import PASoundness.PAtoCompactCandidateAlphaLeast

/-! K alpha conversion of only the least-subset nonemptiness binder in the
exact candidate. This does not assert induction or an arithmetic domain. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateNonemptyAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateAlphaLeast
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Replace the least-subset nonemptiness binder `l` by fresh `x`, while
leaving the other candidate components and their binders untouched. -/
def candidate_nonempty_rename (y b p q u t l m r x : Nat)
    (fresh : [y,u,t,l,m,r,x].Nodup) :
    KDerivation (imp (candidateCode y b p q u t l m r)
      (candidateCode y b p q u t x m r)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let D := candidateCode y b p q u t l m r
  have hd : Context [D] D := Context.head [] D
  have ht : Context [D] (oneLevelTransitiveCode y b p q) := Context.conjunctionLeft hd
  have hg : Context [D] (greatestSubsetsCode y u t m r) :=
    Context.conjunctionLeft (Context.conjunctionRight hd)
  have hl : Context [D] (leastSubsetsCode y u t l m r) :=
    Context.conjunctionRight (Context.conjunctionRight hd)
  have hl' : Context [D] (leastSubsetsCode y u t x m r) :=
    .mp hl (.closed (least_subsets_nonempty_rename y u t l m r x fresh))
  exact Context.conjunctionIntro ht (Context.conjunctionIntro hg hl')

theorem candidate_nonempty_rename_certificate (y b p q u t l m r x : Nat)
    (fresh : [y,u,t,l,m,r,x].Nodup) :
    theoremCode (certificate (candidate_nonempty_rename y b p q u t l m r x fresh)) =
      imp (candidateCode y b p q u t l m r) (candidateCode y b p q u t x m r) :=
  certificate_correct (candidate_nonempty_rename y b p q u t l m r x fresh)

end PASoundness.PAtoCompactCandidateNonemptyAlpha

#print axioms PASoundness.PAtoCompactCandidateNonemptyAlpha.candidate_nonempty_rename
#print axioms PASoundness.PAtoCompactCandidateNonemptyAlpha.candidate_nonempty_rename_certificate
