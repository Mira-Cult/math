import PASoundness.PAtoCompactMixedCandidateBounds

/-! Discharge the generic candidate-alpha freshness inputs for the four fixed
mixed comparisons used by the seeded span. The premise is the literal
candidate code on each whole; the outputs are the exact shaped candidates. -/
namespace PASoundness.PAtoCompactMixedCandidateFixedAlignment

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactPairFilter
open PASoundness.PAtoCompactLocalPairFresh PASoundness.PAtoCompactMixedGuardFromCandidates
open PASoundness.PAtoCompactMixedCandidateAlignment PASoundness.PAtoCompactMixedCandidateBounds
open PASoundness.PAtoCompactAdditionGenericMixedOrder

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle
  PASoundness.PAtoCompactPairFilter.pairWitness
  PASoundness.PAtoCompactPairFilter.pairPredicate
  PASoundness.PAtoCompactFilteredSubset.filterPredicate

def sourceCandidate : Nat := candidateCode 0 37 32 33 34 30 35 13 36
def targetCandidate : Nat := candidateCode 8 37 32 33 34 30 35 13 36

private theorem bound_over_40 (c t : Nat) (ht : 11 ≤ t) (h : 4 * t < c) : 40 < c := by omega

private theorem source_fields_fresh (c : Nat) (hc : 40 < c) :
    [0,34,30,13,36,c+1].Nodup ∧ [0,34,30,35,13,36,c+1].Nodup ∧
    [0,c+1,30,13,36,29].Nodup ∧ [0,c+1,30,35,13,36,29].Nodup ∧
    [0,c+1,29,35,13,36,c+2].Nodup ∧ [0,c+1,29,13,36,c+3].Nodup ∧
    [0,c+1,29,c+2,13,36,c+3].Nodup ∧ [0,c+1,29,c+3,36,c+4].Nodup ∧
    [0,c+1,29,c+2,c+3,36,c+4].Nodup := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
    not_false_eq_true,List.nodup_nil,and_true]
  repeat' apply And.intro
  all_goals omega

private theorem target_fields_fresh (c : Nat) (hc : 40 < c) :
    [8,34,30,13,36,c+1].Nodup ∧ [8,34,30,35,13,36,c+1].Nodup ∧
    [8,c+1,30,13,36,39].Nodup ∧ [8,c+1,30,35,13,36,39].Nodup ∧
    [8,c+1,39,35,13,36,c+2].Nodup ∧ [8,c+1,39,13,36,c+3].Nodup ∧
    [8,c+1,39,c+2,13,36,c+3].Nodup ∧ [8,c+1,39,c+3,36,c+4].Nodup ∧
    [8,c+1,39,c+2,c+3,36,c+4].Nodup := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
    not_false_eq_true,List.nodup_nil,and_true]
  repeat' apply And.intro
  all_goals omega

/-- Align the actual source candidate for old point 2 and new point 26. -/
def source_forward_alignment : KDerivation
    (imp sourceCandidate (shapedCandidate 0 0 40 2 26 37)) := by
  let c := pairWitness 0 (testName 0 2 26) 2 26
  have hb : 4 * 29 < c := pair_witness_test_quad 0 (testName 0 2 26) 2 26
  have hf := source_fields_fresh c (bound_over_40 c 29 (by decide) hb)
  exact candidate_to_mixed_shape 0 40 2 26 37 32 33 34 30 35 13 36 (by decide)
    hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.1
    hf.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2.2

/-- Align the same source candidate for old point 26 and new point 2. -/
def source_reverse_alignment : KDerivation
    (imp sourceCandidate (shapedCandidate 0 0 40 26 2 37)) := by
  let c := pairWitness 0 (testName 0 26 2) 26 2
  have hb : 4 * 29 < c := pair_witness_test_quad 0 (testName 0 26 2) 26 2
  have hf := source_fields_fresh c (bound_over_40 c 29 (by decide) hb)
  exact candidate_to_mixed_shape 0 40 26 2 37 32 33 34 30 35 13 36 (by decide)
    hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.1
    hf.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2.2

/-- Align the actual target candidate for old point 3 and new point 27. -/
def target_forward_alignment : KDerivation
    (imp targetCandidate (shapedCandidate 8 8 41 3 27 37)) := by
  let c := pairWitness 8 (testName 8 3 27) 3 27
  have hb : 4 * 39 < c := pair_witness_test_quad 8 (testName 8 3 27) 3 27
  have hf := target_fields_fresh c (bound_over_40 c 39 (by decide) hb)
  exact candidate_to_mixed_shape 8 41 3 27 37 32 33 34 30 35 13 36 (by decide)
    hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.1
    hf.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2.2

/-- Align the same target candidate for old point 27 and new point 3. -/
def target_reverse_alignment : KDerivation
    (imp targetCandidate (shapedCandidate 8 8 41 27 3 37)) := by
  let c := pairWitness 8 (testName 8 27 3) 27 3
  have hb : 4 * 39 < c := pair_witness_test_quad 8 (testName 8 27 3) 27 3
  have hf := target_fields_fresh c (bound_over_40 c 39 (by decide) hb)
  exact candidate_to_mixed_shape 8 41 27 3 37 32 33 34 30 35 13 36 (by decide)
    hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2.1
    hf.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2.2

end PASoundness.PAtoCompactMixedCandidateFixedAlignment

#print axioms PASoundness.PAtoCompactMixedCandidateFixedAlignment.sourceCandidate
#print axioms PASoundness.PAtoCompactMixedCandidateFixedAlignment.targetCandidate
#print axioms PASoundness.PAtoCompactMixedCandidateFixedAlignment.source_forward_alignment
#print axioms PASoundness.PAtoCompactMixedCandidateFixedAlignment.source_reverse_alignment
#print axioms PASoundness.PAtoCompactMixedCandidateFixedAlignment.target_forward_alignment
#print axioms PASoundness.PAtoCompactMixedCandidateFixedAlignment.target_reverse_alignment
