import Sude.FWGrowthPermutedTraceMidpoints
import Sude.FWFourFamilyStageTotals

/-! Exact full-stage growth mean on the same trace-placed square. This is not
the mean of the residual ordinary labels after rectangle selection. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768

/-- A stage-preserving permutation of all growth labels leaves the full stage
midpoint mean equal to the average over the trace stage's actual low set. -/
theorem growth_trace_placed_full_stage_mean
    {n Q g : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (cells : (Fin stages.length × Fin Q) × Bool → Cell n) (a : Cell n ≃ Fin (n*n))
    (ω : Fin stages.length → Equiv.Perm (Fin Q))
    (hplaced : ∀ x, entry a (cells x) = (trace.poolValues rfl hpool (stagePairPermutation ω x)).val)
    (j : Fin stages.length) :
    (∑ i, (((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2)) / (Q : ℝ) =
      (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / (Q : ℝ) := by
  classical
  have hmid := (growth_permuted_trace_midpoints trace rfl hpool cells a ω hplaced).2.2
  have hlow : Finset.univ.image (trace.lowAt rfl j) = (stages.get j).lows := by
    exact Finset.image_orderEmbOfFin_univ _ _
  have hsum : (∑ i, growthStageMidpoint (stages.get j) (trace.lowAt rfl j (ω j i))) =
      ∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p := by
    calc
      _ = ∑ i, growthStageMidpoint (stages.get j) (trace.lowAt rfl j i) :=
        Equiv.sum_comp (ω j) _
      _ = _ := by
        have hinj : Function.Injective (trace.lowAt rfl j) := (Finset.orderEmbOfFin _ _).injective
        rw [← hlow, Finset.sum_image hinj.injOn]
  congr 1
  calc
    _ = ∑ i, growthStageMidpoint (stages.get j) (trace.lowAt rfl j (ω j i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hmid j i
    _ = _ := hsum

/-- The growth component of the original four-family physical-stage mean is
the full lows mean of the same trace-stage occurrence and placement. -/
theorem fw_four_family_growth_stage_mean
    {n L g : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g (6 * (n+8)) initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + stages.length * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (a : Cell n ≃ Fin (n*n)) (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (hplaced : ∀ x, entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc x) =
      (trace.poolValues rfl hpool (stagePairPermutation ω x)).val)
    (j : Fin stages.length) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n stages.length
    (∑ i, (((entry a (cells ((Sum.inr j,i),false)) : ℝ) +
      entry a (cells ((Sum.inr j,i),true))) / 2)) / ((6*(n+8) : ℕ) : ℝ) =
      (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / ((6*(n+8) : ℕ) : ℝ) := by
  exact growth_trace_placed_full_stage_mean trace hpool _ a ω hplaced j

end
end Sude
