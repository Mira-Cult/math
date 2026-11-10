import PASoundness.PAtoCompactCandidateFieldTransport
import PASoundness.PAtoCompactCandidateAlphaTrans
import PASoundness.PAtoCompactCandidateReflexiveObject

/-! Explicit K alpha bridge between the symmetry and reflexivity candidate
predicates at a common fresh object name. Binder collisions are handled in a
specified order; this does not prove transitivity, congruence, or PA transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateBinderBridge
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateFieldTransport
open PASoundness.PAtoCompactCandidateAlphaTrans PASoundness.PAtoCompactCandidateReflexiveObject

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rename the two transitivity-test binders in the entire candidate. -/
def transitivity_field (x b p q a k l m g s t : Nat)
    (fresh : [x,b,p,q,s,t].Nodup) :
    KDerivation (imp (candidateCode x b p q a k l m g)
      (candidateCode x b s t a k l m g)) :=
  candidate_map _ _ _ _ _ _ (one_level_tests_rename x b p q s t fresh)
    (CompactHilbertBasis.identity _) (CompactHilbertBasis.identity _)

/-- K derives the reflexivity candidate from the symmetry candidate at name
8. Temporary subset binder 50 avoids cross-field binder collisions. -/
def symmetry_to_reflexivity_candidate : KDerivation
    (imp (candidateCode 8 37 32 33 34 30 35 10 36)
      (candidateCode 8 41 37 38 32 0 31 34 35)) := by
  have h1 := subset_test_field 8 37 32 33 34 30 35 10 36 0 (by decide) (by decide)
  have h2 := subset_field 8 37 32 33 34 0 35 10 36 50 (by decide) (by decide)
  have h3 := witness_field 8 37 32 33 50 0 35 10 36 34 (by decide) (by decide)
  have h4 := nonempty_field 8 37 32 33 50 0 35 34 36 31 (by decide)
  have h5 := order_field 8 37 32 33 50 0 31 34 36 35 (by decide) (by decide)
  have h6 := member_field 8 37 32 33 50 0 31 34 35 41 (by decide)
  have h7 := transitivity_field 8 41 32 33 50 0 31 34 35 37 38 (by decide)
  have h8 := subset_field 8 41 37 38 50 0 31 34 35 32 (by decide) (by decide)
  exact compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6 (compose h7 h8))))))

/-- Reflexivity is available under the exact candidate predicate used by the
symmetry proof after both are placed at object name 8. -/
def reflexivity_under_symmetry_candidate : KDerivation
    (imp (candidateCode 8 37 32 33 34 30 35 10 36) reflexive8.encode) :=
  compose symmetry_to_reflexivity_candidate reflexivity_at_eight

theorem reflexivity_under_symmetry_candidate_certificate :
    theoremCode (certificate reflexivity_under_symmetry_candidate) =
      imp (candidateCode 8 37 32 33 34 30 35 10 36) reflexive8.encode :=
  certificate_correct reflexivity_under_symmetry_candidate

end PASoundness.PAtoCompactCandidateBinderBridge

#print axioms PASoundness.PAtoCompactCandidateBinderBridge.symmetry_to_reflexivity_candidate
#print axioms PASoundness.PAtoCompactCandidateBinderBridge.reflexivity_under_symmetry_candidate
#print axioms PASoundness.PAtoCompactCandidateBinderBridge.reflexivity_under_symmetry_candidate_certificate
