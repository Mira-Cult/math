import PASoundness.PAtoCompactMultiplicationCanonicalSuccessorClosed
import PASoundness.PAtoCompactMultiplicationExtensionTargetRebase
import PASoundness.PAtoCompactMultiplicationCandidateTotalityFromAnchored

/-! Candidate-guarded K multiplication-output existence at fixed names.
The construction supplies the actual first-factor successor derivation,
reallocates it to the induction interface, and applies the previously proved
candidate-restricted induction. This is not arbitrary-label term-graph
existence, product functionality, the second-factor PA axiom, or PA soundness.
It uses finite K proof data rather than metatheoretic soundness. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCandidateTotalityClosed
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMultiplicationCanonicalSuccessorClosed
open PASoundness.PAtoCompactMultiplicationExtensionTargetRebase
open PASoundness.PAtoCompactMultiplicationCandidateTotalityFromAnchored
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Candidate inputs named 200 and 30 have a candidate product at the bound
output name 32. The labels differ syntactically; their values may coincide.
No multiplication-successor or induction proof is supplied as a parameter. -/
noncomputable def candidate_total : KDerivation
    (imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode))) :=
  candidate_totality_from_anchored (extension_from_canonical canonical_successor)

theorem candidate_total_certificate : theoremCode (certificate candidate_total) =
    imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode)) :=
  certificate_correct candidate_total
end PASoundness.PAtoCompactMultiplicationCandidateTotalityClosed
#print axioms PASoundness.PAtoCompactMultiplicationCandidateTotalityClosed.candidate_total
#print axioms PASoundness.PAtoCompactMultiplicationCandidateTotalityClosed.candidate_total_certificate
