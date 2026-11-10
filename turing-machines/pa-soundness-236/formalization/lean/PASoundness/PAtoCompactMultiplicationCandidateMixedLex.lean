import PASoundness.PAtoCompactMultiplicationCandidateMixedOrder
import PASoundness.PAtoCompactMultiplicationMixedLexLogic
import PASoundness.PAtoCompactRawSuccBridge

/-! Candidate-guarded pointwise old/new lexicographic comparisons for the
fixed-cut multiplication extension. This constructs no row or product graph
and does not establish multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationCandidateMixedLex
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactRawSuccBridge
open PASoundness.PAtoCompactMultiplicationCandidateMixedOrder
open PASoundness.PAtoCompactMultiplicationMixedLexLogic
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Three candidate guards, an anchored cut and suffix, the old/new target
memberships, and the old/new first-coordinate relation suffice for both mixed
lex comparisons. No global comparison or suffix transitivity is used. -/
def candidate_mixed_lex : KDerivation
    (imp (domainAt 100 45).encode (imp (domainAt 100 32).encode
      (imp (domainAt 100 31).encode (imp (either (equal 32 45) (member 45 32))
        (imp (filterGraph 45 40 35 (neg (member 32 35)))
          (imp (member 32 5) (imp (member 40 9) (imp (member 31 3)
            (imp (equal 7 31) (both forwardComparison reverseComparison)))))))))) := by
  have htrans : KDerivation (imp (domainAt 100 31).encode (transitiveCode 31 42 43)) := by
    have h := candidate_transitive_frame 100 38 31 (by decide) (by decide) (by decide)
    simpa [namedTransitive, transitiveBody, transitiveCode, Formula.encode] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 7 31,member 31 3,member 40 9,member 32 5,
    filterGraph 45 40 35 (neg (member 32 35)),either (equal 32 45) (member 45 32),
    (domainAt 100 31).encode,(domainAt 100 32).encode,(domainAt 100 45).encode]
  have he : Context Γ (equal 7 31) := .head _ _
  have hs : Context Γ (member 31 3) := .hypothesis (by simp [Γ])
  have hn : Context Γ (member 40 9) := .hypothesis (by simp [Γ])
  have ho : Context Γ (member 32 5) := .hypothesis (by simp [Γ])
  have hf : Context Γ (filterGraph 45 40 35 (neg (member 32 35))) := .hypothesis (by simp [Γ])
  have hc : Context Γ (either (equal 32 45) (member 45 32)) := .hypothesis (by simp [Γ])
  have hd31 : Context Γ (domainAt 100 31).encode := .hypothesis (by simp [Γ])
  have hd32 : Context Γ (domainAt 100 32).encode := .hypothesis (by simp [Γ])
  have hd45 : Context Γ (domainAt 100 45).encode := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode 31 42 43) := .mp hd31 (.closed htrans)
  have horder : Context Γ (both (member 9 5) (neg (member 5 9))) :=
    .mp hn (.mp ho (.mp hf (.mp hc (.mp hd32 (.mp hd45 (.closed candidate_old_before_new))))))
  exact .mp (Context.conjunctionRight horder)
    (.mp (Context.conjunctionLeft horder) (.mp he (.mp hs (.mp ht (.closed mixed_lex)))))

theorem candidate_mixed_lex_certificate : theoremCode (certificate candidate_mixed_lex) =
    imp (domainAt 100 45).encode (imp (domainAt 100 32).encode
      (imp (domainAt 100 31).encode (imp (either (equal 32 45) (member 45 32))
        (imp (filterGraph 45 40 35 (neg (member 32 35)))
          (imp (member 32 5) (imp (member 40 9) (imp (member 31 3)
            (imp (equal 7 31) (both forwardComparison reverseComparison))))))))) :=
  certificate_correct candidate_mixed_lex
end PASoundness.PAtoCompactMultiplicationCandidateMixedLex
#print axioms PASoundness.PAtoCompactMultiplicationCandidateMixedLex.candidate_mixed_lex
#print axioms PASoundness.PAtoCompactMultiplicationCandidateMixedLex.candidate_mixed_lex_certificate
