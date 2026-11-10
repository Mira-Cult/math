import PASoundness.PAtoCompactMultiplicationCandidateMixedLex
import PASoundness.PAtoCompactFilterInstantiation

/-! Capture-safe specialization of the old/new multiplication lex point
comparison to the row invariant's first-factor label 30. This is a local K
proof and does not construct the row, graph case split or product totality. -/
namespace PASoundness.PAtoCompactMultiplicationActualMixedLex
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactMultiplicationMixedLexLogic
open PASoundness.PAtoCompactMultiplicationCandidateMixedLex
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp PASoundness.Cantor.pair PASoundness.Cantor.triangle

private def Lf : Formula := namedEither (.member 7 3) (namedBoth (.equal 3 7) (.member 8 4))
private def Lr : Formula := namedEither (.member 3 7) (namedBoth (.equal 7 3) (.member 4 8))
private def Cf : Formula := namedBoth (.imp (.member 9 5) Lf) (.imp Lf (.member 9 5))
private def Cr : Formula := namedBoth (.imp (.member 5 9) Lr) (.imp Lr (.member 5 9))
private def Filter : Formula := .all 35 (namedFilterBody 45 40 35 (Formula.member 32 35).not)
private def source : Formula := .imp (domainAt 100 45) (.imp (domainAt 100 32)
  (.imp (domainAt 100 31) (.imp (namedEither (.equal 32 45) (.member 45 32))
    (.imp Filter (.imp (.member 32 5) (.imp (.member 40 9) (.imp (.member 31 3)
      (.imp (.equal 7 31) (namedBoth Cf Cr)))))))))
private def target : Formula := .imp (domainAt 100 45) (.imp (domainAt 100 32)
  (.imp (domainAt 100 30) (.imp (namedEither (.equal 32 45) (.member 45 32))
    (.imp Filter (.imp (.member 32 5) (.imp (.member 40 9) (.imp (.member 30 3)
      (.imp (.equal 7 30) (namedBoth Cf Cr)))))))))

private def source_proof : KDerivation source.encode := by
  simpa [source,Filter,Cf,Cr,Lf,Lr,namedFilterBody,filterGraph,filterPredicate,namedBoth,namedEither,
    Formula.not,Formula.encode,both,neg,either,forwardComparison,reverseComparison,oldToNewLex,newToOldLex]
    using candidate_mixed_lex

/-- The candidate source factor is 30, matching the fixed-first row invariant.
The other candidate and cut/suffix hypotheses are unchanged. -/
def candidate_mixed_lex_30 : KDerivation
    (imp (domainAt 100 45).encode (imp (domainAt 100 32).encode
      (imp (domainAt 100 30).encode (imp (either (equal 32 45) (member 45 32))
        (imp (filterGraph 45 40 35 (neg (member 32 35)))
          (imp (member 32 5) (imp (member 40 9) (imp (member 30 3)
            (imp (equal 7 30) (both forwardComparison reverseComparison)))))))))) := by
  have hi := universalInstance 31 30 source (by decide) (by decide) (by decide)
  have hr : replace 31 30 source = target := by decide
  rw [hr] at hi
  have h : KDerivation target.encode := .mp (.generalize 31 source_proof) hi
  simpa [target,Filter,Cf,Cr,Lf,Lr,namedFilterBody,filterGraph,filterPredicate,namedBoth,namedEither,
    Formula.not,Formula.encode,both,neg,either,forwardComparison,reverseComparison,oldToNewLex,newToOldLex] using h

theorem candidate_mixed_lex_30_certificate : theoremCode (certificate candidate_mixed_lex_30) =
    imp (domainAt 100 45).encode (imp (domainAt 100 32).encode
      (imp (domainAt 100 30).encode (imp (either (equal 32 45) (member 45 32))
        (imp (filterGraph 45 40 35 (neg (member 32 35)))
          (imp (member 32 5) (imp (member 40 9) (imp (member 30 3)
            (imp (equal 7 30) (both forwardComparison reverseComparison))))))))) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationActualMixedLex
#print axioms PASoundness.PAtoCompactMultiplicationActualMixedLex.candidate_mixed_lex_30
#print axioms PASoundness.PAtoCompactMultiplicationActualMixedLex.candidate_mixed_lex_30_certificate
