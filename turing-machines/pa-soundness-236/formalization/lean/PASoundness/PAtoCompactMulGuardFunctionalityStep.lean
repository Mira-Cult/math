import PASoundness.PAtoCompactMulBinaryFunctionalSameBase
import PASoundness.PAtoCompactGuardFunctionalityCrossBase

/-! Structural multiplication case for guarded term-graph functionality.
The two child functionality families remain explicit proof-data inputs. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMulGuardFunctionalityStep

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep
open PASoundness.PAtoCompactTermSubstPolyReplacement PASoundness.PAtoCompactGuardFunctionalityCrossBase
open PASoundness.PAtoCompactMulBinaryFunctionalSameBase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Guarded functionality is closed under a multiplication node, given the
two child functionality families. No multiplication functionality premise is
assumed; the source-output domain is extracted from the actual graph. -/
noncomputable def mul_guard_functionality (g : Formula) (t u : Peano.Term)
    (leftFunctional : GuardFunctionality g t) (rightFunctional : GuardFunctionality g u) :
    GuardFunctionality g (binaryTerm false t u) := by
  intro b p q hp hq hvars hg hdom
  let c := b + termCost t + termCost u + 100
  let d := c + 64 + termCost t + termCost u + 100
  have hbc : b + 1 < c := by dsimp [c]; omega
  have hmemL (a : Nat) (ha : a ∈ t.varFinset) : a ∈ (binaryTerm false t u).varFinset := by
    simp only [binaryTerm, Bool.false_eq_true, ↓reduceIte, Term.varFinset,
      Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨0, by simpa using ha⟩
  have hmemR (a : Nat) (ha : a ∈ u.varFinset) : a ∈ (binaryTerm false t u).varFinset := by
    simp only [binaryTerm, Bool.false_eq_true, ↓reduceIte, Term.varFinset,
      Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨1, by simpa using ha⟩
  have ht : ∀ a ∈ t.varFinset, a < b := by intro a ha; exact hvars a (hmemL a ha)
  have hu : ∀ a ∈ u.varFinset, a < b := by intro a ha; exact hvars a (hmemR a ha)
  have hdomL : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b a).encode) := by
    intro a ha
    exact hdom a (hmemL a ha)
  have hdomR : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt b a).encode) := by
    intro a ha
    exact hdom a (hmemR a ha)
  have hbd : b ≤ d := by dsimp [d, c]; omega
  have hb_d : b < d := by dsimp [d, c]; omega
  have hc_d : c < d := by dsimp [d]; omega
  have hc1_d : c + 1 < d := by dsimp [d]; omega
  have hleft := cross_base g t b (b+64) (c+64) d b c
    (by omega) (by omega) hbd (by omega) (by omega) hb_d hc_d ht hg hdomL leftFunctional
  have hright := cross_base g u b (b+64+termCost t) (c+64+termCost t) d (b+1) (c+1)
    (by omega) (by omega) hbd (by omega) (by omega) (by omega) hc1_d hu hg hdomR rightFunctional
  exact mul_functionality_same_base id t u b c p q d b g hbc hp hq ht hu hg
    (by omega) (by omega) (by omega) (by omega) hleft hright

end PASoundness.PAtoCompactMulGuardFunctionalityStep

#print axioms PASoundness.PAtoCompactMulGuardFunctionalityStep.mul_guard_functionality
