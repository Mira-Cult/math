import PASoundness.PAtoCompactSeededSpanSeedTargetUnique
import PASoundness.PAtoCompactSeededSpanCleanEndpoints

/-! Supply both seed/seed uniqueness branches from the actual seed bijection
and stored-pair cleanliness. The two path/path uniqueness implications,
suffix guards, seeded invariant and actual point memberships/edges remain
explicit inputs; this is still pointwise and does not prove totality. -/
namespace PASoundness.PAtoCompactSeededSpanPointUniquenessSeed

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSeededSpanBase
open PASoundness.PAtoCompactSeededSpanPointOrder PASoundness.PAtoCompactSeededSpanPointUniqueness
open PASoundness.PAtoCompactSeededSpanSeedSourceUnique PASoundness.PAtoCompactSeededSpanSeedTargetUnique
open PASoundness.PAtoCompactSeededSpanCleanEndpoints PASoundness.PAtoCompactFirstSpanPathOutside
open PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def assumptions : List Nat := [(graphFormula 9 26 27).encode,(graphFormula 9 2 3).encode,
  both (member 0 26) (member 8 27),both (member 0 2) (member 8 3),pathTargetUnique,pathSourceUnique,
  targetGuard.encode,outsideGuard.encode,seedClean.encode,seededSpan.encode,seedBijection.encode]

private def from_seed_context : Context assumptions pointUniqueness := by
  let Γ := assumptions
  have he2 : Context Γ (graphFormula 9 26 27).encode := .head _ _
  have he1 : Context Γ (graphFormula 9 2 3).encode := .hypothesis (by simp [Γ,assumptions])
  have hd2 : Context Γ (both (member 0 26) (member 8 27)) := .hypothesis (by simp [Γ,assumptions])
  have hd1 : Context Γ (both (member 0 2) (member 8 3)) := .hypothesis (by simp [Γ,assumptions])
  have hpt : Context Γ pathTargetUnique := .hypothesis (by simp [Γ,assumptions])
  have hps : Context Γ pathSourceUnique := .hypothesis (by simp [Γ,assumptions])
  have ht : Context Γ targetGuard.encode := .hypothesis (by simp [Γ,assumptions])
  have hs : Context Γ outsideGuard.encode := .hypothesis (by simp [Γ,assumptions])
  have hc : Context Γ seedClean.encode := .hypothesis (by simp [Γ,assumptions])
  have hi : Context Γ seededSpan.encode := .hypothesis (by simp [Γ,assumptions])
  have hb : Context Γ seedBijection.encode := .hypothesis (by simp [Γ,assumptions])
  have hend : Context Γ seedEndpoints := .mp hc (.closed seed_endpoints_from_clean)
  have hss : Context Γ seedSourceUnique := .mp hend (.mp hb (.closed seed_source_unique_from_bijection))
  have hst : Context Γ seedTargetUnique := .mp hend (.mp hb (.closed seed_target_unique_from_bijection))
  exact .mp he2 (.mp he1 (.mp hd2 (.mp hd1 (.mp hpt (.mp hst (.mp hps (.mp hss
    (.mp ht (.mp hs (.mp hend (.mp hi (.closed point_uniqueness))))))))))))

/-- Pointwise source/target uniqueness with the seed cases discharged. -/
def point_uniqueness_from_seed : KDerivation (imp seedBijection.encode (imp seededSpan.encode
    (imp seedClean.encode (imp outsideGuard.encode (imp targetGuard.encode
      (imp pathSourceUnique (imp pathTargetUnique (imp (both (member 0 2) (member 8 3))
        (imp (both (member 0 26) (member 8 27)) (imp (graphFormula 9 2 3).encode
          (imp (graphFormula 9 26 27).encode pointUniqueness))))))))))) := by
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
  exact from_seed_context

end PASoundness.PAtoCompactSeededSpanPointUniquenessSeed

#print axioms PASoundness.PAtoCompactSeededSpanPointUniquenessSeed.point_uniqueness_from_seed
