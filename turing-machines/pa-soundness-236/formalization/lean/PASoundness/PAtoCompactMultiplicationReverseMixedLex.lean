import PASoundness.PAtoCompactMultiplicationSwappedOutputOrder
import PASoundness.PAtoCompactMultiplicationReverseMixedLexLogic
import PASoundness.PAtoCompactRawSuccBridge

/-! Candidate-guarded mixed lexicographic comparison when the first queried
point is in the new row and the second is in the old graph. The explicit cut
and suffix hypotheses are retained; no graph construction or multiplication
totality is asserted. -/
namespace PASoundness.PAtoCompactMultiplicationReverseMixedLex
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactRawSuccBridge
open PASoundness.PAtoCompactMultiplicationMixedLexLogic
open PASoundness.PAtoCompactMultiplicationReverseMixedLexLogic
open PASoundness.PAtoCompactMultiplicationSwappedOutputOrder
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- New point `(3,4,5)` has major coordinate equal to old factor 30 and
output 5 in the suffix. Old point `(7,8,9)` has major coordinate in 30
and output 9 in the cut. Both exact lex comparisons follow in K. -/
def candidate_reverse_mixed_lex : KDerivation
    (imp (domainAt 100 45).encode (imp (domainAt 100 32).encode
      (imp (domainAt 100 30).encode (imp (either (equal 32 45) (member 45 32))
        (imp (filterGraph 45 40 35 (neg (member 32 35)))
          (imp (member 32 9) (imp (member 40 5) (imp (member 30 7)
            (imp (equal 3 30) (both forwardComparison reverseComparison)))))))))) := by
  have htrans : KDerivation (imp (domainAt 100 30).encode (transitiveCode 30 42 43)) := by
    have h := candidate_transitive_frame 100 38 30 (by decide) (by decide) (by decide)
    simpa [namedTransitive,transitiveBody,transitiveCode,Formula.encode] using h
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
  let Γ := [equal 3 30,member 30 7,member 40 5,member 32 9,
    filterGraph 45 40 35 (neg (member 32 35)),either (equal 32 45) (member 45 32),
    (domainAt 100 30).encode,(domainAt 100 32).encode,(domainAt 100 45).encode]
  have he : Context Γ (equal 3 30) := .head _ _
  have hs : Context Γ (member 30 7) := .hypothesis (by simp [Γ])
  have hn : Context Γ (member 40 5) := .hypothesis (by simp [Γ])
  have ho : Context Γ (member 32 9) := .hypothesis (by simp [Γ])
  have hf : Context Γ (filterGraph 45 40 35 (neg (member 32 35))) := .hypothesis (by simp [Γ])
  have hc : Context Γ (either (equal 32 45) (member 45 32)) := .hypothesis (by simp [Γ])
  have hd30 : Context Γ (domainAt 100 30).encode := .hypothesis (by simp [Γ])
  have hd32 : Context Γ (domainAt 100 32).encode := .hypothesis (by simp [Γ])
  have hd45 : Context Γ (domainAt 100 45).encode := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode 30 42 43) := .mp hd30 (.closed htrans)
  have horder : Context Γ (both (member 5 9) (neg (member 9 5))) :=
    .mp hn (.mp ho (.mp hf (.mp hc (.mp hd32 (.mp hd45 (.closed swapped_old_before_new))))))
  exact .mp (Context.conjunctionRight horder)
    (.mp (Context.conjunctionLeft horder) (.mp he (.mp hs (.mp ht (.closed reverse_mixed_lex)))))

theorem candidate_reverse_mixed_lex_certificate :
    theoremCode (certificate candidate_reverse_mixed_lex) =
      imp (domainAt 100 45).encode (imp (domainAt 100 32).encode
        (imp (domainAt 100 30).encode (imp (either (equal 32 45) (member 45 32))
          (imp (filterGraph 45 40 35 (neg (member 32 35)))
            (imp (member 32 9) (imp (member 40 5) (imp (member 30 7)
              (imp (equal 3 30) (both forwardComparison reverseComparison))))))))) :=
  certificate_correct candidate_reverse_mixed_lex
end PASoundness.PAtoCompactMultiplicationReverseMixedLex
#print axioms PASoundness.PAtoCompactMultiplicationReverseMixedLex.candidate_reverse_mixed_lex
#print axioms PASoundness.PAtoCompactMultiplicationReverseMixedLex.candidate_reverse_mixed_lex_certificate
