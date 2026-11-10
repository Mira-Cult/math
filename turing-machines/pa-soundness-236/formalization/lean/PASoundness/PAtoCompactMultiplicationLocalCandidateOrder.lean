import PASoundness.PAtoCompactLocalCompare
import PASoundness.PAtoCompactPairFilterBounds
import PASoundness.PAtoCompactRawSuccBridge
import PASoundness.PAtoCompactGuardBaseTransport

/-! Local comparison of two members of the same explicit candidate result.
The least-subsets field uses the candidate's existing binders; this is not
comparability across different candidates or a multiplication theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationLocalCandidateOrder
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateBinderBridge PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactRawSuccBridge
open PASoundness.PAtoCompactLocalCompare PASoundness.PAtoCompactPairFilter
open PASoundness.PAtoCompactPairFilterBounds PASoundness.PAtoCompactFilteredSubset
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The generated pair-filter witness does not collide with any fixed name
in the local candidate and comparison formulas. -/
theorem pair_fresh : [45,136,5,9,135,137,138,139,pairWitness 45 136 5 9].Nodup := by
  have hb := (pair_witness_bounds 45 136 5 9).2.1
  have hm : pairWitness 45 136 5 9 % 4 = 0 := by
    simp [pairWitness, filterPredicate, both, neg, imp]
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true]
  omega

/-- The least-subsets field of the actual candidate guard proves that two
members of result 45 are comparable. -/
def candidate_comparable : KDerivation (imp (domainAt 100 45).encode
    (imp (member 45 5) (imp (member 45 9)
      (either (equal 5 9) (either (member 9 5) (member 5 9)))))) := by
  have h := local_comparable 45 136 5 9 135 137 138 139 pair_fresh
  rw [domainAt_encode]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let D := candidateCode 45 132 133 134 135 136 137 138 139
  let Γ := [member 45 9, member 45 5, D]
  have hb : Context Γ (member 45 9) := .head _ _
  have ha : Context Γ (member 45 5) := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hl := Context.conjunctionRight (Context.conjunctionRight hd)
  exact .mp hb (.mp ha (.mp hl (.closed h)))

/-- The old cut is transitive from its candidate guard, in names suited to
pointwise comparison. -/
def cut_transitive : KDerivation (imp (domainAt 100 32).encode (transitiveCode 32 54 55)) := by
  have h := candidate_transitive_frame 100 50 32 (by decide) (by decide) (by decide)
  simpa [namedTransitive, transitiveBody, transitiveCode, Formula.encode] using h

/-- The new result is transitive from its candidate guard. -/
def result_transitive : KDerivation (imp (domainAt 100 45).encode (transitiveCode 45 54 55)) := by
  have h := candidate_transitive_frame 100 50 45 (by decide) (by decide) (by decide)
  simpa [namedTransitive, transitiveBody, transitiveCode, Formula.encode] using h

theorem candidate_comparable_certificate : theoremCode (certificate candidate_comparable) =
    imp (domainAt 100 45).encode (imp (member 45 5) (imp (member 45 9)
      (either (equal 5 9) (either (member 9 5) (member 5 9))))) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationLocalCandidateOrder
#print axioms PASoundness.PAtoCompactMultiplicationLocalCandidateOrder.candidate_comparable
#print axioms PASoundness.PAtoCompactMultiplicationLocalCandidateOrder.cut_transitive
#print axioms PASoundness.PAtoCompactMultiplicationLocalCandidateOrder.result_transitive
#print axioms PASoundness.PAtoCompactMultiplicationLocalCandidateOrder.candidate_comparable_certificate
