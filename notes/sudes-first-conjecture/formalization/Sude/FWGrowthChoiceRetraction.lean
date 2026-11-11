import Sude.FWGrowthRectangleChoice

/-! Reapply the realized growth-stage rectangle choices using the complete
larger witness choice as fallback. Equality is global, including unused
rectangle labels. -/
namespace Sude
noncomputable section

/-- The full larger reserved choice is a fixed point of the realized-stage
choice override, including at every unused rectangle. -/
theorem fw_growth_choice_retract_larger_reservation {n L P M : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hmax : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + M * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hle : P ≤ M) (other : Fin L → Bool) :
    fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff
      (fwBridgeSeedWideGrowthChoice hrect hseed hwide hmax other) =
    fwBridgeSeedWideGrowthChoice hrect hseed hwide hmax other := by
  classical
  let prior := fwBridgeSeedWideGrowthChoice hrect hseed hwide hmax other
  change fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff prior = prior
  funext x
  by_cases hb : ∃ t, bridgeDiagonalRectangle hrect t = x
  · obtain ⟨t, rfl⟩ := hb
    obtain ⟨⟨j,i⟩, rfl⟩ := (finProdFinEquiv : Fin 5 × Fin (4 * 6) ≃ Fin (5 * (4 * 6))).surjective t
    rw [fwBridgeSeedWideGrowthChoice_bridge hrect hseed hwide hoff prior j i]
    exact (fwBridgeSeedWideGrowthChoice_bridge hrect hseed hwide hmax other j i).symm
  by_cases hs : ∃ t, fwSeedRectangle hseed t = x
  · obtain ⟨t, rfl⟩ := hs
    obtain ⟨⟨j,i⟩, rfl⟩ := (finProdFinEquiv : Fin 16 × Fin (4 * 6) ≃ Fin (16 * (4 * 6))).surjective t
    rw [fwBridgeSeedWideGrowthChoice_seed hrect hseed hwide hoff prior j i]
    exact (fwBridgeSeedWideGrowthChoice_seed hrect hseed hwide hmax other j i).symm
  by_cases hw : ∃ t, fwWideRectangle hwide t = x
  · obtain ⟨t, rfl⟩ := hw
    obtain ⟨⟨j,i⟩, rfl⟩ := (finProdFinEquiv : Fin (3 * (n / 450)) × Fin (4 * 6) ≃ Fin ((3 * (n / 450)) * (4 * 6))).surjective t
    rw [fwBridgeSeedWideGrowthChoice_wide hrect hseed hwide hoff prior j i]
    exact (fwBridgeSeedWideGrowthChoice_wide hrect hseed hwide hmax other j i).symm
  by_cases hg : ∃ t, fwGrowthRectangle hoff t = x
  · obtain ⟨t, rfl⟩ := hg
    obtain ⟨⟨j,i⟩, rfl⟩ := (finProdFinEquiv : Fin P × Fin (4 * 6) ≃ Fin (P * (4 * 6))).surjective t
    rw [fwBridgeSeedWideGrowthChoice_growth hrect hseed hwide hoff prior j i]
    have h := fwBridgeSeedWideGrowthChoice_offset_restrict hrect hseed hwide hmax hoff hle other j i
    change prior (fwGrowthRectangle hoff (finProdFinEquiv (j,i))) = decide (i.val < 2 * 6) at h
    exact h.symm
  exact fwBridgeSeedWideGrowthChoice_outside hrect hseed hwide hoff prior x hb hs hw hg


/-- The same global retraction in the explicit nesting used by the source
theta witness; the fallback is its complete prior rectangle choice. -/
theorem fw_theta_witness_choice_retract_realized {n L P M : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hmax : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + M * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hle : P ≤ M) (other : Fin L → Bool) :
    let prior := fwBridgeSeedRectangleChoice hrect hseed
      (fwWideRectangleChoice hwide (fwGrowthRectangleChoice hmax other))
    fwBridgeSeedWideGrowthChoice hrect hseed hwide hoff prior = prior := by
  simpa only [fwBridgeSeedWideGrowthChoice, fwBridgeSeedWideRectangleChoice] using
    fw_growth_choice_retract_larger_reservation hrect hseed hwide hmax hoff hle other

end
end Sude
