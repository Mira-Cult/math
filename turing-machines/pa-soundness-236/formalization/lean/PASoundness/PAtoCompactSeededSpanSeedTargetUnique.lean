import PASoundness.PAtoCompactSeededSpanSeedSourceUnique
import PASoundness.PAtoCompactConditionalTransitivityFirstInverse

/-! The seed/seed target-injectivity branch from the supplied seed bijection
and conditional seed endpoint memberships. No graph construction or path/path
injectivity is asserted. -/
namespace PASoundness.PAtoCompactSeededSpanSeedTargetUnique

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactConditionalTransitivityFirstInverse
open PASoundness.PAtoCompactConditionalTransitivityUniqueness
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSeededSpanOrderCases PASoundness.PAtoCompactSeededSpanPointOrder
open PASoundness.PAtoCompactSeededSpanPointUniqueness PASoundness.PAtoCompactSeededSpanSeedSourceUnique

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def localBody : Formula := .imp (.member 1 10) (.imp (.member 0 2)
  (.imp (.member 0 4) (.imp (graphFormula 6 2 10)
    (.imp (graphFormula 6 4 10) (.equal 2 4)))))
private def frame : Formula := .imp bijectionFormula (.imp (.member 1 10) localBody)
private def moved40 : Formula := replace 0 40 frame
private def moved41 : Formula := replace 1 41 moved40
private def seedLocal : Formula := replace 6 14 (replace 1 41 (replace 0 40 localBody))
private def point : Formula := .imp (.member 41 10) seedLocal
private def at3 : Formula := replace 10 3 point
private def at26 : Formula := replace 4 26 at3
private theorem at26_alignment : at26 = .imp (.member 41 3) (.imp (.member 41 3)
    (.imp (.member 40 2) (.imp (.member 40 26) (.imp (graphFormula 14 2 3)
      (.imp (graphFormula 14 26 3) (.equal 2 26)))))) := by decide

private def local_from_seed : KDerivation (imp seedBijection.encode point.encode) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame,localBody,firstInverseUnique,Formula.encode] using first_inverse_unique_of_bijection
  have h40 := replace_derivation 0 40 frame (by decide) (by decide) hbase
  have h41 := replace_derivation 1 41 moved40 (by decide) (by decide) (by simpa only [moved40] using h40)
  have h14 := replace_derivation 6 14 moved41 (by decide) (by decide) (by simpa only [moved41] using h41)
  have ha : replace 6 14 moved41 = .imp seedBijection point := by decide
  rw [ha] at h14
  exact h14

private def local_at_points : KDerivation (imp seedBijection.encode at26.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [seedBijection.encode]
  have hb : Context Γ seedBijection.encode := .head _ _
  have hlocal : Context Γ point.encode := .mp hb (.closed local_from_seed)
  have hv (v : Nat) (freshB : v ∉ seedBijection.free) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    have he : h = seedBijection.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity v seedBijection freshB
  have hall : Context Γ (allCode 10 (allCode 4 point.encode)) :=
    Context.generalize 10 (hv 10 (by decide)) (Context.generalize 4 (hv 4 (by decide)) hlocal)
  have h10 := universalInstance 10 3 (.all 4 point) (by decide) (by decide) (by decide)
  have ha10 : replace 10 3 (.all 4 point) = .all 4 at3 := by decide
  rw [ha10] at h10
  have h4 := universalInstance 4 26 at3 (by decide) (by decide) (by decide)
  have ha4 : replace 4 26 at3 = at26 := by rfl
  rw [ha4] at h4
  exact .mp (.mp hall (.closed h10)) (.closed h4)

/-- The seed bijection and conditional endpoint memberships prove
target-injectivity for the two actual seed edges. -/
def seed_target_unique_from_bijection : KDerivation
    (imp seedBijection.encode (imp seedEndpoints seedTargetUnique)) := by
  have ht := (equalityReplace 27 3 (graphFormula 14 26 27) (by decide) (by decide)).1
  have ha : replace 27 3 (graphFormula 14 26 27) = graphFormula 14 26 3 := by decide
  rw [ha] at ht
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 3 27,secondSeed,firstSeed,seedEndpoints,seedBijection.encode]
  have he : Context Γ (equal 3 27) := .head _ _
  have hs2 : Context Γ secondSeed := .hypothesis (by simp [Γ])
  have hs1 : Context Γ firstSeed := .hypothesis (by simp [Γ])
  have hend : Context Γ seedEndpoints := .hypothesis (by simp [Γ])
  have hb : Context Γ seedBijection.encode := .hypothesis (by simp [Γ])
  have hm1 : Context Γ (both (member 40 2) (member 41 3)) := .mp hs1 (Context.conjunctionLeft hend)
  have hm2 : Context Γ (both (member 40 26) (member 41 27)) := .mp hs2 (Context.conjunctionRight hend)
  have h2 : Context Γ (member 40 2) := Context.conjunctionLeft hm1
  have h26 : Context Γ (member 40 26) := Context.conjunctionLeft hm2
  have h3 : Context Γ (member 41 3) := Context.conjunctionRight hm1
  have he2 : Context Γ (graphFormula 14 26 3).encode := .mp hs2 (.mp (Context.eqSymm he) (.closed ht))
  have hlocal : Context Γ at26.encode := .mp hb (.closed local_at_points)
  have hgoal : Context Γ (imp (member 41 3) (imp (member 41 3) (imp (member 40 2)
      (imp (member 40 26) (imp (graphFormula 14 2 3).encode
        (imp (graphFormula 14 26 3).encode (equal 2 26))))))) := by
    simpa only [at26_alignment,Formula.encode] using hlocal
  exact .mp he2 (.mp hs1 (.mp h26 (.mp h2 (.mp h3 (.mp h3 hgoal)))))

theorem seed_target_unique_from_bijection_certificate :
    theoremCode (certificate seed_target_unique_from_bijection) =
      imp seedBijection.encode (imp seedEndpoints seedTargetUnique) :=
  certificate_correct seed_target_unique_from_bijection

end PASoundness.PAtoCompactSeededSpanSeedTargetUnique

#print axioms PASoundness.PAtoCompactSeededSpanSeedTargetUnique.seed_target_unique_from_bijection
#print axioms PASoundness.PAtoCompactSeededSpanSeedTargetUnique.seed_target_unique_from_bijection_certificate
