import PASoundness.PAtoCompactGuardBaseTransport

/-! Exact candidate binder alignment needed for the restricted addition
induction step. Every binder change is a literal K proof; name 204 is above
the target's block but distinct from every binder in it. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionInductionCandidateAlign
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateFieldTransport PASoundness.PAtoCompactCandidateBinderBridge
open PASoundness.PAtoCompactGuardBaseTransport
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The predecessor candidate supplied by the restricted induction engine
matches the fixed `domainAt 100 204` guard after alpha-converting all eight
private candidate binders. This does not assume any semantic soundness. -/
def predecessor_guard_align : KDerivation
    (imp (candidateCode 204 230 209 210 232 31 203 231 206)
      (domainAt 100 204).encode) := by
  have h1 := transitivity_field 204 230 209 210 232 31 203 231 206 133 134 (by decide)
  have h2 := member_field 204 230 133 134 232 31 203 231 206 132 (by decide)
  have h3 := subset_field 204 132 133 134 232 31 203 231 206 135 (by decide) (by decide)
  have h4 := subset_test_field 204 132 133 134 135 31 203 231 206 136 (by decide) (by decide)
  have h5 := nonempty_field 204 132 133 134 135 136 203 231 206 137 (by decide)
  have h6 := witness_field 204 132 133 134 135 136 137 231 206 138 (by decide) (by decide)
  have h7 := order_field 204 132 133 134 135 136 137 138 206 139 (by decide) (by decide)
  rw [domainAt_encode]
  exact compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6 h7)))))

theorem predecessor_guard_align_certificate : theoremCode (certificate predecessor_guard_align) =
    imp (candidateCode 204 230 209 210 232 31 203 231 206)
      (domainAt 100 204).encode := certificate_correct predecessor_guard_align
end PASoundness.PAtoCompactAdditionInductionCandidateAlign
#print axioms PASoundness.PAtoCompactAdditionInductionCandidateAlign.predecessor_guard_align
#print axioms PASoundness.PAtoCompactAdditionInductionCandidateAlign.predecessor_guard_align_certificate
