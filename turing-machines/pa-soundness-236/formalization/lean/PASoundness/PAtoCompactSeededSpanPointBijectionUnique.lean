import PASoundness.PAtoCompactSeededSpanPathUniqueness
import PASoundness.PAtoCompactSeededSpanPointUniquenessSeed

/-! Pointwise source and target uniqueness from the actual seed and suffix
bijections, supplied clean graphs and filters, and the actual seeded invariant.
This does not yet prove either direction of graph totality or global bijection. -/
namespace PASoundness.PAtoCompactSeededSpanPointBijectionUnique

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSeededSpanBase
open PASoundness.PAtoCompactSeededSpanPointUniqueness PASoundness.PAtoCompactSeededSpanPointUniquenessSeed
open PASoundness.PAtoCompactSeededSpanSeedSourceUnique PASoundness.PAtoCompactSeededSpanCleanEndpoints
open PASoundness.PAtoCompactSeededSpanPathUniqueness PASoundness.PAtoCompactSelectedPathUniquenessFromBijections
open PASoundness.PAtoCompactFirstSpanPathOutside PASoundness.PAtoCompactFirstSpanTargetOutside
open PASoundness.PAtoCompactSuffixCleanGraphGuard

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def assumptions : List Nat := [(graphFormula 9 26 27).encode,(graphFormula 9 2 3).encode,
  both (member 0 26) (member 8 27),both (member 0 2) (member 8 3),secondBijection.encode,
  firstBijection.encode,targetGuard.encode,outsideGuard.encode,seedClean.encode,seededSpan.encode,seedBijection.encode]

private def point_context : Context assumptions pointUniqueness := by
  let Γ := assumptions
  have he2 : Context Γ (graphFormula 9 26 27).encode := .head _ _
  have he1 : Context Γ (graphFormula 9 2 3).encode := .hypothesis (by simp [Γ,assumptions])
  have hd2 : Context Γ (both (member 0 26) (member 8 27)) := .hypothesis (by simp [Γ,assumptions])
  have hd1 : Context Γ (both (member 0 2) (member 8 3)) := .hypothesis (by simp [Γ,assumptions])
  have hsecond : Context Γ secondBijection.encode := .hypothesis (by simp [Γ,assumptions])
  have hfirst : Context Γ firstBijection.encode := .hypothesis (by simp [Γ,assumptions])
  have ht : Context Γ targetGuard.encode := .hypothesis (by simp [Γ,assumptions])
  have hs : Context Γ outsideGuard.encode := .hypothesis (by simp [Γ,assumptions])
  have hc : Context Γ seedClean.encode := .hypothesis (by simp [Γ,assumptions])
  have hi : Context Γ seededSpan.encode := .hypothesis (by simp [Γ,assumptions])
  have hb : Context Γ seedBijection.encode := .hypothesis (by simp [Γ,assumptions])
  have hsc : Context Γ storedClean.encode := Context.conjunctionLeft hs
  have htc : Context Γ targetClean.encode := Context.conjunctionLeft ht
  have hpathGuard : Context Γ pathGuard.encode := Context.conjunctionIntro hfirst
    (Context.conjunctionIntro hsc (Context.conjunctionIntro hsecond (Context.conjunctionIntro htc
      (Context.conjunctionIntro (Context.conjunctionLeft hd1) (Context.conjunctionIntro (Context.conjunctionLeft hd2)
        (Context.conjunctionIntro (Context.conjunctionRight hd1) (Context.conjunctionRight hd2)))))))
  have hpaths : Context Γ (both pathSourceUnique pathTargetUnique) :=
    .mp hpathGuard (.closed path_uniqueness_from_bijections)
  have hps : Context Γ pathSourceUnique := Context.conjunctionLeft hpaths
  have hpt : Context Γ pathTargetUnique := Context.conjunctionRight hpaths
  exact .mp he2 (.mp he1 (.mp hd2 (.mp hd1 (.mp hpt (.mp hps (.mp ht (.mp hs
    (.mp hc (.mp hi (.mp hb (.closed point_uniqueness_from_seed)))))))))))

/-- Both equality directions for two actual graph-9 edges, conditional on
the displayed seed/suffix bijections, clean/filter guards and invariant. -/
def point_bijection_unique : KDerivation (imp seedBijection.encode (imp seededSpan.encode
    (imp seedClean.encode (imp outsideGuard.encode (imp targetGuard.encode
      (imp firstBijection.encode (imp secondBijection.encode (imp (both (member 0 2) (member 8 3))
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
  exact point_context

theorem point_bijection_unique_certificate : theoremCode (certificate point_bijection_unique) =
    imp seedBijection.encode (imp seededSpan.encode (imp seedClean.encode (imp outsideGuard.encode
      (imp targetGuard.encode (imp firstBijection.encode (imp secondBijection.encode
        (imp (both (member 0 2) (member 8 3)) (imp (both (member 0 26) (member 8 27))
          (imp (graphFormula 9 2 3).encode (imp (graphFormula 9 26 27).encode pointUniqueness)))))))))) :=
  certificate_correct point_bijection_unique

end PASoundness.PAtoCompactSeededSpanPointBijectionUnique

#print axioms PASoundness.PAtoCompactSeededSpanPointBijectionUnique.point_bijection_unique
#print axioms PASoundness.PAtoCompactSeededSpanPointBijectionUnique.point_bijection_unique_certificate
