import PASoundness.PAtoCompactMixedGuardArbitraryCut
import PASoundness.PAtoCompactSeededSpanCleanEndpoints
import PASoundness.PAtoCompactSecondSpanPathOutside
import PASoundness.PAtoCompactSecondSpanTargetOutside

/-! Construct the four conditional mixed-order guards from supplied shaped
whole candidates, supplied cut candidates and cut relations, the actual
seed-edge endpoint condition, whole endpoint memberships, and the two clean
suffix/filter guards. The specific whole-candidate binder alignment remains
an explicit input. -/
namespace PASoundness.PAtoCompactSeededSpanMixedGuards

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactMixedGuardFromCandidates PASoundness.PAtoCompactMixedGuardArbitraryCut
open PASoundness.PAtoCompactSeededSpanOrderCases PASoundness.PAtoCompactSeededSpanMixedOrder
open PASoundness.PAtoCompactSeededSpanPointOrder PASoundness.PAtoCompactSeededSpanPathOrder
open PASoundness.PAtoCompactFirstSpanPathOutside PASoundness.PAtoCompactSecondSpanPathOutside
open PASoundness.PAtoCompactFirstSpanTargetOutside PASoundness.PAtoCompactSecondSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceForwardCandidate : Nat := shapedCandidate 0 0 40 2 26 37
def sourceReverseCandidate : Nat := shapedCandidate 0 0 40 26 2 37
def targetForwardCandidate : Nat := shapedCandidate 8 8 41 3 27 37
def targetReverseCandidate : Nat := shapedCandidate 8 8 41 27 3 37
def sourceCutCandidate : Nat := candidateCode 40 37 32 33 34 30 35 13 36
def targetCutCandidate : Nat := candidateCode 41 37 32 33 34 30 35 13 36
def sourceCutRelation : Nat := either (equal 40 0) (member 0 40)
def targetCutRelation : Nat := either (equal 41 8) (member 8 41)

private def assumptions : List Nat := [orderGuard.encode,seedEndpoints,targetGuard.encode,
  outsideGuard.encode,targetCutRelation,sourceCutRelation,targetCutCandidate,sourceCutCandidate,
  targetReverseCandidate,targetForwardCandidate,sourceReverseCandidate,sourceForwardCandidate]

/-- Each mixed case is built using its actual seed edge and path. Candidate
codes, cut relations, seed endpoint implications, whole memberships and both
clean suffix/filter guards are explicit context assumptions. -/
private def mixed_guards_context : Context assumptions (mixedPremises 40 41) := by
  let Γ := assumptions
  have hforwardSource : Context Γ (imp firstSeed (imp secondPath (forwardSourceGuard 40))) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := secondPath :: firstSeed :: Γ
    have hp : Context Δ secondPath := .head _ _
    have hs : Context Δ firstSeed := .hypothesis (by simp [Δ])
    have hend : Context Δ seedEndpoints := .hypothesis (by simp [Δ,Γ,assumptions])
    have ho : Context Δ orderGuard.encode := .hypothesis (by simp [Δ,Γ,assumptions])
    have hc : Context Δ outsideGuard.encode := .hypothesis (by simp [Δ,Γ,assumptions])
    have hr : Context Δ sourceCutRelation := .hypothesis (by simp [Δ,Γ,assumptions])
    have hcut : Context Δ sourceCutCandidate := .hypothesis (by simp [Δ,Γ,assumptions])
    have hw : Context Δ sourceForwardCandidate := .hypothesis (by simp [Δ,Γ,assumptions])
    have hm : Context Δ (both (member 40 2) (member 41 3)) := .mp hs (Context.conjunctionLeft hend)
    have hwhole : Context Δ (member 0 26) := Context.conjunctionLeft
      (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight ho)))
    have hout : Context Δ (neg (member 40 26)) := .mp hp (.mp hc (.closed second_path_source_outside))
    exact .mp hout (.mp hwhole (.mp (Context.conjunctionLeft hm) (.mp hr (.mp hcut (.mp hw
      (.closed (mixed_guard_from_cut_candidate 0 40 2 26 37 37 32 33 34 30 35 13 36 (by decide))))))))
  have hforwardTarget : Context Γ (imp firstSeed (imp secondPath (forwardTargetGuard 41))) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := secondPath :: firstSeed :: Γ
    have hp : Context Δ secondPath := .head _ _
    have hs : Context Δ firstSeed := .hypothesis (by simp [Δ])
    have hend : Context Δ seedEndpoints := .hypothesis (by simp [Δ,Γ,assumptions])
    have ho : Context Δ orderGuard.encode := .hypothesis (by simp [Δ,Γ,assumptions])
    have hc : Context Δ targetGuard.encode := .hypothesis (by simp [Δ,Γ,assumptions])
    have hr : Context Δ targetCutRelation := .hypothesis (by simp [Δ,Γ,assumptions])
    have hcut : Context Δ targetCutCandidate := .hypothesis (by simp [Δ,Γ,assumptions])
    have hw : Context Δ targetForwardCandidate := .hypothesis (by simp [Δ,Γ,assumptions])
    have hm : Context Δ (both (member 40 2) (member 41 3)) := .mp hs (Context.conjunctionLeft hend)
    have hwhole : Context Δ (member 8 27) := Context.conjunctionRight
      (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight ho))))
    have hout : Context Δ (neg (member 41 27)) := .mp hp (.mp hc (.closed second_path_target_outside))
    exact .mp hout (.mp hwhole (.mp (Context.conjunctionRight hm) (.mp hr (.mp hcut (.mp hw
      (.closed (mixed_guard_from_cut_candidate 8 41 3 27 37 37 32 33 34 30 35 13 36 (by decide))))))))
  have hreverseSource : Context Γ (imp firstPath (imp secondSeed (reverseSourceGuard 40))) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := secondSeed :: firstPath :: Γ
    have hs : Context Δ secondSeed := .head _ _
    have hp : Context Δ firstPath := .hypothesis (by simp [Δ])
    have hend : Context Δ seedEndpoints := .hypothesis (by simp [Δ,Γ,assumptions])
    have ho : Context Δ orderGuard.encode := .hypothesis (by simp [Δ,Γ,assumptions])
    have hc : Context Δ outsideGuard.encode := .hypothesis (by simp [Δ,Γ,assumptions])
    have hr : Context Δ sourceCutRelation := .hypothesis (by simp [Δ,Γ,assumptions])
    have hcut : Context Δ sourceCutCandidate := .hypothesis (by simp [Δ,Γ,assumptions])
    have hw : Context Δ sourceReverseCandidate := .hypothesis (by simp [Δ,Γ,assumptions])
    have hm : Context Δ (both (member 40 26) (member 41 27)) := .mp hs (Context.conjunctionRight hend)
    have hwhole : Context Δ (member 0 2) := Context.conjunctionLeft
      (Context.conjunctionRight (Context.conjunctionRight ho))
    have hout : Context Δ (neg (member 40 2)) := .mp hp (.mp hc (.closed first_path_source_outside))
    exact .mp hout (.mp hwhole (.mp (Context.conjunctionLeft hm) (.mp hr (.mp hcut (.mp hw
      (.closed (mixed_guard_from_cut_candidate 0 40 26 2 37 37 32 33 34 30 35 13 36 (by decide))))))))
  have hreverseTarget : Context Γ (imp firstPath (imp secondSeed (reverseTargetGuard 41))) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := secondSeed :: firstPath :: Γ
    have hs : Context Δ secondSeed := .head _ _
    have hp : Context Δ firstPath := .hypothesis (by simp [Δ])
    have hend : Context Δ seedEndpoints := .hypothesis (by simp [Δ,Γ,assumptions])
    have ho : Context Δ orderGuard.encode := .hypothesis (by simp [Δ,Γ,assumptions])
    have hc : Context Δ targetGuard.encode := .hypothesis (by simp [Δ,Γ,assumptions])
    have hr : Context Δ targetCutRelation := .hypothesis (by simp [Δ,Γ,assumptions])
    have hcut : Context Δ targetCutCandidate := .hypothesis (by simp [Δ,Γ,assumptions])
    have hw : Context Δ targetReverseCandidate := .hypothesis (by simp [Δ,Γ,assumptions])
    have hm : Context Δ (both (member 40 26) (member 41 27)) := .mp hs (Context.conjunctionRight hend)
    have hwhole : Context Δ (member 8 3) := Context.conjunctionLeft
      (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight ho))))
    have hout : Context Δ (neg (member 41 3)) := .mp hp (.mp hc (.closed first_path_target_outside))
    exact .mp hout (.mp hwhole (.mp (Context.conjunctionRight hm) (.mp hr (.mp hcut (.mp hw
      (.closed (mixed_guard_from_cut_candidate 8 41 27 3 37 37 32 33 34 30 35 13 36 (by decide))))))))
  exact Context.conjunctionIntro hforwardSource (Context.conjunctionIntro hforwardTarget
    (Context.conjunctionIntro hreverseSource hreverseTarget))

/-- Curried form of the same literal assumptions and four mixed implications. -/
def mixed_guards : KDerivation (imp sourceForwardCandidate (imp sourceReverseCandidate
    (imp targetForwardCandidate (imp targetReverseCandidate (imp sourceCutCandidate
      (imp targetCutCandidate (imp sourceCutRelation (imp targetCutRelation
        (imp outsideGuard.encode (imp targetGuard.encode (imp seedEndpoints
          (imp orderGuard.encode (mixedPremises 40 41))))))))))))) := by
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
  apply Context.deduction
  apply Context.deduction
  exact mixed_guards_context

theorem mixed_guards_certificate : theoremCode (certificate mixed_guards) =
    imp sourceForwardCandidate (imp sourceReverseCandidate (imp targetForwardCandidate
      (imp targetReverseCandidate (imp sourceCutCandidate (imp targetCutCandidate
        (imp sourceCutRelation (imp targetCutRelation (imp outsideGuard.encode
          (imp targetGuard.encode (imp seedEndpoints (imp orderGuard.encode (mixedPremises 40 41)))))))))))) :=
  certificate_correct mixed_guards

end PASoundness.PAtoCompactSeededSpanMixedGuards

#print axioms PASoundness.PAtoCompactSeededSpanMixedGuards.sourceForwardCandidate
#print axioms PASoundness.PAtoCompactSeededSpanMixedGuards.sourceReverseCandidate
#print axioms PASoundness.PAtoCompactSeededSpanMixedGuards.targetForwardCandidate
#print axioms PASoundness.PAtoCompactSeededSpanMixedGuards.targetReverseCandidate
#print axioms PASoundness.PAtoCompactSeededSpanMixedGuards.sourceCutCandidate
#print axioms PASoundness.PAtoCompactSeededSpanMixedGuards.targetCutCandidate
#print axioms PASoundness.PAtoCompactSeededSpanMixedGuards.sourceCutRelation
#print axioms PASoundness.PAtoCompactSeededSpanMixedGuards.targetCutRelation
#print axioms PASoundness.PAtoCompactSeededSpanMixedGuards.mixed_guards
#print axioms PASoundness.PAtoCompactSeededSpanMixedGuards.mixed_guards_certificate
