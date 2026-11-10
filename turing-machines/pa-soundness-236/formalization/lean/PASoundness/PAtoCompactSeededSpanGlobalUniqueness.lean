import PASoundness.PAtoCompactSeededSpanPointBijectionUnique
import PASoundness.PAtoCompactSeededSpanGlobalOrderPoint
import PASoundness.PAtoCompactFreeVacuity

/-! Quantified graph uniqueness under a fixed named guard containing the
actual seed/suffix bijections, clean/filter guards and seeded invariant. This
is not forward or reverse coverage and does not by itself establish a full
bijection. -/
namespace PASoundness.PAtoCompactSeededSpanGlobalUniqueness

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSeededSpanBase PASoundness.PAtoCompactSeededSpanSeedSourceUnique
open PASoundness.PAtoCompactSeededSpanCleanEndpoints PASoundness.PAtoCompactFirstSpanPathOutside
open PASoundness.PAtoCompactFirstSpanTargetOutside PASoundness.PAtoCompactSelectedPathUniquenessFromBijections
open PASoundness.PAtoCompactSeededSpanPointUniqueness PASoundness.PAtoCompactSeededSpanPointBijectionUnique
open PASoundness.PAtoCompactSeededSpanGlobalOrderPoint

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def globalGuard : Formula := namedBoth seedBijection (namedBoth seededSpan (namedBoth seedClean
  (namedBoth outsideGuard (namedBoth targetGuard (namedBoth firstBijection secondBijection)))))
def pointComparison : Formula := namedBoth (.imp (.equal 2 26) (.equal 3 27))
  (.imp (.equal 3 27) (.equal 2 26))
def pointClause : Formula := .imp PASoundness.PAtoCompactSeededSpanGlobalOrderPoint.pointGuard pointComparison
def quantifiedUniqueness : Formula := .all 2 (.all 26 (.all 3 (.all 27 pointClause)))

/-- Under the same global guard, the actual point's four memberships and two
graph edges imply both source and target equality uniqueness. -/
def global_uniqueness_point : KDerivation (imp globalGuard.encode pointClause.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let pointGuard := PASoundness.PAtoCompactSeededSpanGlobalOrderPoint.pointGuard
  let Γ := [pointGuard.encode,globalGuard.encode]
  have hp : Context Γ pointGuard.encode := .head _ _
  have hg : Context Γ globalGuard.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ seedBijection.encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hi : Context Γ seededSpan.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hc : Context Γ seedClean.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hs : Context Γ outsideGuard.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have ht : Context Γ targetGuard.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hf : Context Γ firstBijection.encode := Context.conjunctionLeft hr
  have hsecond : Context Γ secondBijection.encode := Context.conjunctionRight hr
  have hm02 : Context Γ (member 0 2) := Context.conjunctionLeft hp
  have hp := Context.conjunctionRight hp
  have hm026 : Context Γ (member 0 26) := Context.conjunctionLeft hp
  have hp := Context.conjunctionRight hp
  have hm83 : Context Γ (member 8 3) := Context.conjunctionLeft hp
  have hp := Context.conjunctionRight hp
  have hm827 : Context Γ (member 8 27) := Context.conjunctionLeft hp
  have hp := Context.conjunctionRight hp
  have he1 : Context Γ (graphFormula 9 2 3).encode := Context.conjunctionLeft hp
  have he2 : Context Γ (graphFormula 9 26 27).encode := Context.conjunctionRight hp
  have hd1 : Context Γ (both (member 0 2) (member 8 3)) := Context.conjunctionIntro hm02 hm83
  have hd2 : Context Γ (both (member 0 26) (member 8 27)) := Context.conjunctionIntro hm026 hm827
  exact .mp he2 (.mp he1 (.mp hd2 (.mp hd1 (.mp hsecond (.mp hf (.mp ht (.mp hs
    (.mp hc (.mp hi (.mp hb (.closed point_bijection_unique)))))))))))

/-- Universal pointwise source/target uniqueness under the identical global
guard; the fresh bound-label order is 2,26,3,27. -/
def global_uniqueness_lift : KDerivation (imp globalGuard.encode quantifiedUniqueness.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [globalGuard.encode]
  have hg : Context Γ globalGuard.encode := .head _ _
  have hp : Context Γ pointClause.encode := .mp hg (.closed global_uniqueness_point)
  have hv (v : Nat) (fresh : v ∉ globalGuard.free) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    have he : h = globalGuard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity v globalGuard fresh
  have hall := Context.generalize 2 (hv 2 (by decide))
    (Context.generalize 26 (hv 26 (by decide))
      (Context.generalize 3 (hv 3 (by decide))
        (Context.generalize 27 (hv 27 (by decide)) hp)))
  simpa only [quantifiedUniqueness,Formula.encode] using hall

theorem global_uniqueness_lift_certificate : theoremCode (certificate global_uniqueness_lift) =
    imp globalGuard.encode quantifiedUniqueness.encode := certificate_correct global_uniqueness_lift

end PASoundness.PAtoCompactSeededSpanGlobalUniqueness

#print axioms PASoundness.PAtoCompactSeededSpanGlobalUniqueness.globalGuard
#print axioms PASoundness.PAtoCompactSeededSpanGlobalUniqueness.pointComparison
#print axioms PASoundness.PAtoCompactSeededSpanGlobalUniqueness.pointClause
#print axioms PASoundness.PAtoCompactSeededSpanGlobalUniqueness.quantifiedUniqueness
#print axioms PASoundness.PAtoCompactSeededSpanGlobalUniqueness.global_uniqueness_point
#print axioms PASoundness.PAtoCompactSeededSpanGlobalUniqueness.global_uniqueness_lift
#print axioms PASoundness.PAtoCompactSeededSpanGlobalUniqueness.global_uniqueness_lift_certificate
