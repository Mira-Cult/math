import PASoundness.PAtoCompactSeededSpanPointUniqueness
import PASoundness.PAtoCompactConditionalTransitivityFirstUnique
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactFreeVacuity

/-! The seed/seed source-functionality branch from an actual seed bijection
and the explicit conditional seed endpoint memberships. The seed bijection is
only assumed; no graph construction or path/path uniqueness is asserted. -/
namespace PASoundness.PAtoCompactSeededSpanSeedSourceUnique

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactConditionalTransitivityFirstUnique
open PASoundness.PAtoCompactConditionalTransitivityUniqueness
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSeededSpanOrderCases PASoundness.PAtoCompactSeededSpanPointOrder
open PASoundness.PAtoCompactSeededSpanPointUniqueness

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def seedBijection : Formula := replace 6 14 (replace 1 41 (replace 0 40 bijectionFormula))
private def localBody : Formula := .imp (.member 0 2) (.imp (.member 1 10)
  (.imp (.member 1 11) (.imp (graphFormula 6 2 10)
    (.imp (graphFormula 6 2 11) (.equal 10 11)))))
private def frame : Formula := .imp bijectionFormula (.imp (.member 0 2) localBody)
private def moved40 : Formula := replace 0 40 frame
private def moved41 : Formula := replace 1 41 moved40
private def seedLocal : Formula := replace 6 14 (replace 1 41 (replace 0 40 localBody))
private def at3 : Formula := replace 10 3 seedLocal
private def at27 : Formula := replace 11 27 at3
private theorem at27_alignment : at27 = .imp (.member 40 2) (.imp (.member 41 3)
    (.imp (.member 41 27) (.imp (graphFormula 14 2 3)
      (.imp (graphFormula 14 2 27) (.equal 3 27))))) := by decide

private def local_from_seed : KDerivation
    (imp seedBijection.encode (imp (member 40 2) seedLocal.encode)) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame,localBody,firstUnique,Formula.encode] using first_unique_of_bijection
  have h40 := replace_derivation 0 40 frame (by decide) (by decide) hbase
  have h41 := replace_derivation 1 41 moved40 (by decide) (by decide) (by simpa only [moved40] using h40)
  have h14 := replace_derivation 6 14 moved41 (by decide) (by decide) (by simpa only [moved41] using h41)
  have ha : replace 6 14 moved41 = .imp seedBijection (.imp (.member 40 2) seedLocal) := by decide
  rw [ha] at h14
  exact h14

private def local_at_points : KDerivation (imp seedBijection.encode
    (imp (member 40 2) at27.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 40 2,seedBijection.encode]
  have hm : Context Γ (member 40 2) := .head _ _
  have hb : Context Γ seedBijection.encode := .hypothesis (by simp [Γ])
  have hlocal : Context Γ seedLocal.encode := .mp hm (.mp hb (.closed local_from_seed))
  have hv (v : Nat) (freshM : v ∉ (Formula.member 40 2).free)
      (freshB : v ∉ seedBijection.free) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = member 40 2
    · subst h; exact free_vacuity v (.member 40 2) freshM
    · have he' : h = seedBijection.encode := hh.resolve_left he
      subst h; exact free_vacuity v seedBijection freshB
  have hall : Context Γ (allCode 10 (allCode 11 seedLocal.encode)) :=
    Context.generalize 10 (hv 10 (by decide) (by decide))
      (Context.generalize 11 (hv 11 (by decide) (by decide)) hlocal)
  have h10 := universalInstance 10 3 (.all 11 seedLocal) (by decide) (by decide) (by decide)
  have ha10 : replace 10 3 (.all 11 seedLocal) = .all 11 at3 := by decide
  rw [ha10] at h10
  have h11 := universalInstance 11 27 at3 (by decide) (by decide) (by decide)
  have ha11 : replace 11 27 at3 = at27 := by rfl
  rw [ha11] at h11
  exact .mp (.mp hall (.closed h10)) (.closed h11)

/-- The seed bijection and the two conditional endpoint implications prove
source-functionality for the two actual seed edges. -/
def seed_source_unique_from_bijection : KDerivation
    (imp seedBijection.encode (imp seedEndpoints seedSourceUnique)) := by
  have ht := (equalityReplace 26 2 (graphFormula 14 26 27) (by decide) (by decide)).1
  have ha : replace 26 2 (graphFormula 14 26 27) = graphFormula 14 2 27 := by decide
  rw [ha] at ht
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 2 26,secondSeed,firstSeed,seedEndpoints,seedBijection.encode]
  have he : Context Γ (equal 2 26) := .head _ _
  have hs2 : Context Γ secondSeed := .hypothesis (by simp [Γ])
  have hs1 : Context Γ firstSeed := .hypothesis (by simp [Γ])
  have hend : Context Γ seedEndpoints := .hypothesis (by simp [Γ])
  have hb : Context Γ seedBijection.encode := .hypothesis (by simp [Γ])
  have hm1 : Context Γ (both (member 40 2) (member 41 3)) := .mp hs1 (Context.conjunctionLeft hend)
  have hm2 : Context Γ (both (member 40 26) (member 41 27)) := .mp hs2 (Context.conjunctionRight hend)
  have hsource : Context Γ (member 40 2) := Context.conjunctionLeft hm1
  have h3 : Context Γ (member 41 3) := Context.conjunctionRight hm1
  have h27 : Context Γ (member 41 27) := Context.conjunctionRight hm2
  have he2 : Context Γ (graphFormula 14 2 27).encode := .mp hs2 (.mp (Context.eqSymm he) (.closed ht))
  have hlocal : Context Γ at27.encode := .mp hsource (.mp hb (.closed local_at_points))
  have hgoal : Context Γ (imp (member 40 2) (imp (member 41 3) (imp (member 41 27)
      (imp (graphFormula 14 2 3).encode (imp (graphFormula 14 2 27).encode (equal 3 27)))))) := by
    simpa only [at27_alignment,Formula.encode] using hlocal
  exact .mp he2 (.mp hs1 (.mp h27 (.mp h3 (.mp hsource hgoal))))

theorem seed_source_unique_from_bijection_certificate :
    theoremCode (certificate seed_source_unique_from_bijection) =
      imp seedBijection.encode (imp seedEndpoints seedSourceUnique) :=
  certificate_correct seed_source_unique_from_bijection

end PASoundness.PAtoCompactSeededSpanSeedSourceUnique

#print axioms PASoundness.PAtoCompactSeededSpanSeedSourceUnique.seedBijection
#print axioms PASoundness.PAtoCompactSeededSpanSeedSourceUnique.seed_source_unique_from_bijection
#print axioms PASoundness.PAtoCompactSeededSpanSeedSourceUnique.seed_source_unique_from_bijection_certificate
