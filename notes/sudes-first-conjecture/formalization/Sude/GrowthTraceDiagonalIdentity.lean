import Sude.GrowthDiagonalMidpointIdentity
import Sude.BTGrowingPermutedPlacement
import Sude.FWGrowthNarrowPD2

/-! Reindex the exact physical diagonal contribution back to the selected
actual low-endpoint labels of the same growth trace. -/
namespace Sude
noncomputable section

/-- If the supplied stage permutation maps each twelve-slot family onto the
selected actual low labels, the same square's growth-cell contribution to
the given line is exactly those selected midpoints minus six times each
stage gap. Line cells outside the supplied growth image are not included. -/
theorem growth_trace_selected_diagonal_identity
    {n P Q g : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q initial radius final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (cells : (Fin P × Fin Q) × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Cell n → Prop) [DecidablePred line] (a : Cell n ≃ Fin (n*n))
    (ω : Fin P → Equiv.Perm (Fin Q)) (S : Fin P → Finset (Fin Q)) (T : Fin P → Finset ℕ)
    (hmap : ∀ j, (S j).image (fun i => trace.lowAt hlen j (ω j i)) = T j)
    (hcard : ∀ j, (S j).card = 12)
    (hweight : ∀ j i, physicalPairLineWeight cells line (j,i) = if i ∈ S j then 1 else 0)
    (horient : ∀ j i, physicalPairLineOrientation cells line (j,i) =
      -(physicalPairLineWeight cells line (j,i)))
    (hplaced : ∀ x, entry a (cells x) =
      (trace.poolValues hlen hpool (stagePairPermutation ω x)).val) :
    (∑ c ∈ (Finset.univ.image cells).filter line, (entry a c : ℝ)) =
      (∑ j, ∑ p ∈ T j, growthStageMidpoint (BTStageTrace.stageAt stages hlen j) p) -
        6 * ∑ j, ((BTStageTrace.stageAt stages hlen j).gap : ℝ) := by
  classical
  have hgap : ∀ j i, entry a (cells ((j,i),true)) = entry a (cells ((j,i),false)) +
      (BTStageTrace.stageAt stages hlen j).gap := by
    intro j i
    rw [hplaced, hplaced]
    exact trace.poolValues_gap hlen hpool j (ω j i)
  rw [growth_diagonal_midpoint_identity cells hcells line a S _ hcard hweight horient hgap]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hinj : Function.Injective (fun i => trace.lowAt hlen j (ω j i)) := by
    have hlow : Function.Injective (trace.lowAt hlen j) := by
      exact ((BTStageTrace.stageAt stages hlen j).lows.orderEmbOfFin
        (trace.stage_properties _ (BTStageTrace.stageAt_mem stages hlen j)).2.2.2.1).injective
    exact hlow.comp (ω j).injective
  have hsum := Finset.sum_image (s := S j)
    (f := fun p => growthStageMidpoint (BTStageTrace.stageAt stages hlen j) p)
    (g := fun i => trace.lowAt hlen j (ω j i)) (fun _ _ _ _ h => hinj h)
  rw [hmap j] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hplaced, hplaced]
  simp [BTGrowingTrace.poolValues, stagePairPermutation, growthStageMidpoint]

end
end Sude
