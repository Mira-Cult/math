import PASoundness.PAtoCompactProductCleanTripleEndpoints
import PASoundness.PAtoCompactTransitiveClosure

/-! Major-coordinate extraction and top-coordinate exclusion for the
explicitly clean old product graph. All statements are finite K proof data;
no extensionality, full product forward clause, multiplication totality, or
PA proof transport is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCleanOldTopExclusion
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductCleanFilter
open PASoundness.PAtoCompactProductCleanTripleEndpoints PASoundness.PAtoCompactProductCleanEndpointsPoint
open PASoundness.PAtoCompactOldTripleEdgeExtract PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Explicit cleanliness of old graph 10 relative to domains 30,31,32. -/
def cleanOld : Formula := .all 19 (.imp (.member 10 19)
  (replace 2 32 (replace 1 31 (replace 0 30 (cleanPredicate 19)))))
private def original : Formula := .imp oldClean (.imp oldTriple (.member 0 3))
private def s0 : Formula := replace 0 30 original
private def s1 : Formula := replace 1 31 s0
private def s2 : Formula := replace 2 32 s1

private def original_proof : KDerivation original.encode := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldTriple.encode, oldClean.encode]
  have ht : Context Γ oldTriple.encode := .head _ _
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have he : Context Γ endpoints.encode := .mp ht (.mp hc (.closed triple_endpoints))
  have he' : Context Γ (both (member 0 3) (both (member 1 4) (member 2 5))) := by
    simpa [endpoints,namedBoth,Formula.not,Formula.encode,both,neg] using he
  exact Context.conjunctionLeft he'

/-- Any actual old-graph triple at labels 3,4,5 has its major coordinate
in old domain 30. The same nested graph witness is used by the imported
endpoint extraction. -/
def old_major : KDerivation (imp cleanOld.encode (imp oldTriple.encode (member 30 3))) := by
  have h0 : KDerivation s0.encode :=
    .mp (.generalize 0 original_proof) (universalInstance 0 30 original (by decide) (by decide) (by decide))
  have h1 : KDerivation s1.encode :=
    .mp (.generalize 1 h0) (universalInstance 1 31 s0 (by decide) (by decide) (by decide))
  have h2 : KDerivation s2.encode :=
    .mp (.generalize 2 h1) (universalInstance 2 32 s1 (by decide) (by decide) (by decide))
  have hs : s2 = .imp cleanOld (.imp oldTriple (.member 30 3)) := by decide
  rw [hs] at h2
  exact h2

/-- A clean old graph cannot contain a triple whose major coordinate 3 is
equal to the old major domain 30. The contradiction is literal compact code 1. -/
def old_top_absurd : KDerivation
    (imp cleanOld.encode (imp (equal 3 30) (imp oldTriple.encode 1))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldTriple.encode,equal 3 30,cleanOld.encode]
  have ht : Context Γ oldTriple.encode := .head _ _
  have he : Context Γ (equal 3 30) := .hypothesis (by simp [Γ])
  have hc : Context Γ cleanOld.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 30 3) := .mp ht (.mp hc (.closed old_major))
  have hs : Context Γ (member 30 30) :=
    .mp he (.mp hm (.closed (memberRightEquality 30 3 30)))
  exact .mp hs (.closed (self_membership_implies_code_one 30))

theorem old_major_certificate : theoremCode (certificate old_major) =
    imp cleanOld.encode (imp oldTriple.encode (member 30 3)) := certificate_correct old_major

theorem old_top_absurd_certificate : theoremCode (certificate old_top_absurd) =
    imp cleanOld.encode (imp (equal 3 30) (imp oldTriple.encode 1)) := certificate_correct old_top_absurd
end PASoundness.PAtoCompactMultiplicationCleanOldTopExclusion
#print axioms PASoundness.PAtoCompactMultiplicationCleanOldTopExclusion.old_major
#print axioms PASoundness.PAtoCompactMultiplicationCleanOldTopExclusion.old_top_absurd
#print axioms PASoundness.PAtoCompactMultiplicationCleanOldTopExclusion.old_major_certificate
#print axioms PASoundness.PAtoCompactMultiplicationCleanOldTopExclusion.old_top_absurd_certificate
