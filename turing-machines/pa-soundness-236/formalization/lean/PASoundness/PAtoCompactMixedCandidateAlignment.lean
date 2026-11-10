import PASoundness.PAtoCompactMixedGuardFromCandidates
import PASoundness.PAtoCompactCandidateFieldTransport
import PASoundness.PAtoCompactCandidateAlphaTrans

/-! Convert a supplied candidate code to the exact candidate-label shape used
by the mixed comparison. Every alpha conversion is finite K proof data, and
every stage's syntactic freshness condition is an explicit Lean input. -/
namespace PASoundness.PAtoCompactMixedCandidateAlignment

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactCandidateFieldTransport PASoundness.PAtoCompactCandidateAlphaTrans
open PASoundness.PAtoCompactLocalPairFresh PASoundness.PAtoCompactPairFilter PASoundness.PAtoCompactAdditionGenericMixedOrder
open PASoundness.PAtoCompactMixedGuardFromCandidates

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Align all candidate binders used by the mixed-order guard. The freshness
premises are syntactic and may require an intermediate alpha-renaming if an
old and a desired label coincide. -/
def candidate_to_mixed_shape (whole cut old new b p q a k l m g : Nat)
    (freshT : [whole,b,p,q,firstTest whole cut old new,secondTest whole cut old new].Nodup)
    (freshAG : [whole,a,k,m,g,(pairWitness whole (testName whole old new) old new)+1].Nodup)
    (freshAL : [whole,a,k,l,m,g,(pairWitness whole (testName whole old new) old new)+1].Nodup)
    (freshKG : [whole,(pairWitness whole (testName whole old new) old new)+1,k,m,g,testName whole old new].Nodup)
    (freshKL : [whole,(pairWitness whole (testName whole old new) old new)+1,k,l,m,g,testName whole old new].Nodup)
    (freshL : [whole,(pairWitness whole (testName whole old new) old new)+1,testName whole old new,l,m,g,
      (pairWitness whole (testName whole old new) old new)+2].Nodup)
    (freshMG : [whole,(pairWitness whole (testName whole old new) old new)+1,testName whole old new,m,g,
      (pairWitness whole (testName whole old new) old new)+3].Nodup)
    (freshML : [whole,(pairWitness whole (testName whole old new) old new)+1,testName whole old new,
      (pairWitness whole (testName whole old new) old new)+2,m,g,
      (pairWitness whole (testName whole old new) old new)+3].Nodup)
    (freshGG : [whole,(pairWitness whole (testName whole old new) old new)+1,testName whole old new,
      (pairWitness whole (testName whole old new) old new)+3,g,
      (pairWitness whole (testName whole old new) old new)+4].Nodup)
    (freshGL : [whole,(pairWitness whole (testName whole old new) old new)+1,testName whole old new,
      (pairWitness whole (testName whole old new) old new)+2,
      (pairWitness whole (testName whole old new) old new)+3,g,
      (pairWitness whole (testName whole old new) old new)+4].Nodup) : KDerivation
    (imp (candidateCode whole b p q a k l m g) (shapedCandidate whole whole cut old new b)) := by
  let P := firstTest whole cut old new
  let Q := secondTest whole cut old new
  let T := testName whole old new
  let C := pairWitness whole T old new
  have ht : KDerivation (imp (candidateCode whole b p q a k l m g)
      (candidateCode whole b P Q a k l m g)) :=
    candidate_map _ _ _ _ _ _ (one_level_tests_rename whole b p q P Q freshT)
      (CompactHilbertBasis.identity _) (CompactHilbertBasis.identity _)
  have ha := subset_field whole b P Q a k l m g (C+1) freshAG freshAL
  have hk := subset_test_field whole b P Q (C+1) k l m g T freshKG freshKL
  have hl := nonempty_field whole b P Q (C+1) T l m g (C+2) freshL
  have hm := witness_field whole b P Q (C+1) T (C+2) m g (C+3) freshMG freshML
  have hg := order_field whole b P Q (C+1) T (C+2) (C+3) g (C+4) freshGG freshGL
  have h := compose ht (compose ha (compose hk (compose hl (compose hm hg))))
  simpa only [shapedCandidate,P,Q,T,C] using h

end PASoundness.PAtoCompactMixedCandidateAlignment

#print axioms PASoundness.PAtoCompactMixedCandidateAlignment.candidate_to_mixed_shape
