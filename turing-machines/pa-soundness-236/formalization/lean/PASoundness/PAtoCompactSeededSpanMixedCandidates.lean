import PASoundness.PAtoCompactSeededSpanMixedGuards
import PASoundness.PAtoCompactMixedCandidateFixedAlignment

/-! Supply the four exact whole-candidate shapes to the mixed-guard
construction by explicit K alpha conversion of the two actual whole
candidate codes. Cut candidates, cut relations, seed-edge membership, whole
endpoint memberships and the clean suffix filters remain explicit. -/
namespace PASoundness.PAtoCompactSeededSpanMixedCandidates

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSeededSpanMixedGuards PASoundness.PAtoCompactMixedCandidateFixedAlignment
open PASoundness.PAtoCompactSeededSpanMixedOrder PASoundness.PAtoCompactSeededSpanPointOrder
open PASoundness.PAtoCompactSeededSpanPathOrder PASoundness.PAtoCompactFirstSpanPathOutside
open PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The two supplied whole candidates yield all four shaped candidates,
without an additional whole-candidate assumption for each orientation. -/
def mixed_guards_from_candidates : KDerivation (imp sourceCandidate (imp targetCandidate
    (imp sourceCutCandidate (imp targetCutCandidate (imp sourceCutRelation (imp targetCutRelation
      (imp outsideGuard.encode (imp targetGuard.encode (imp seedEndpoints
        (imp orderGuard.encode (mixedPremises 40 41))))))))))) := by
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
  apply Context.deduction
  let Γ := [orderGuard.encode,seedEndpoints,targetGuard.encode,outsideGuard.encode,
    targetCutRelation,sourceCutRelation,targetCutCandidate,sourceCutCandidate,targetCandidate,sourceCandidate]
  have ho : Context Γ orderGuard.encode := .head _ _
  have he : Context Γ seedEndpoints := .hypothesis (by simp [Γ])
  have ht : Context Γ targetGuard.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ outsideGuard.encode := .hypothesis (by simp [Γ])
  have hrt : Context Γ targetCutRelation := .hypothesis (by simp [Γ])
  have hrs : Context Γ sourceCutRelation := .hypothesis (by simp [Γ])
  have hct : Context Γ targetCutCandidate := .hypothesis (by simp [Γ])
  have hcs : Context Γ sourceCutCandidate := .hypothesis (by simp [Γ])
  have htarget : Context Γ targetCandidate := .hypothesis (by simp [Γ])
  have hsource : Context Γ sourceCandidate := .hypothesis (by simp [Γ])
  have hsf : Context Γ sourceForwardCandidate := .mp hsource (.closed source_forward_alignment)
  have hsr : Context Γ sourceReverseCandidate := .mp hsource (.closed source_reverse_alignment)
  have htf : Context Γ targetForwardCandidate := .mp htarget (.closed target_forward_alignment)
  have htr : Context Γ targetReverseCandidate := .mp htarget (.closed target_reverse_alignment)
  exact .mp ho (.mp he (.mp ht (.mp hs (.mp hrt (.mp hrs (.mp hct (.mp hcs
    (.mp htr (.mp htf (.mp hsr (.mp hsf (.closed mixed_guards))))))))))))

theorem mixed_guards_from_candidates_certificate :
    theoremCode (certificate mixed_guards_from_candidates) =
      imp sourceCandidate (imp targetCandidate (imp sourceCutCandidate (imp targetCutCandidate
        (imp sourceCutRelation (imp targetCutRelation (imp outsideGuard.encode
          (imp targetGuard.encode (imp seedEndpoints (imp orderGuard.encode (mixedPremises 40 41)))))))))) :=
  certificate_correct mixed_guards_from_candidates

end PASoundness.PAtoCompactSeededSpanMixedCandidates

#print axioms PASoundness.PAtoCompactSeededSpanMixedCandidates.mixed_guards_from_candidates
#print axioms PASoundness.PAtoCompactSeededSpanMixedCandidates.mixed_guards_from_candidates_certificate
