import Sude.FWBridgeWidePairPlacement
import Sude.FWBridgeNumericalStock
import Sude.FWThetaInputs
import Sude.ReservedPoolMean

/-! Same-square bridge midpoint bounds from explicit physical placement,
nominal window validity, and finite theta/RS mean assumptions. -/
namespace Sude
noncomputable section

lemma fw_bridge_window_stock_midpoint (X R : ℝ) (hX : 0 < X) (hR : 0 < R) (l h : ℕ)
    (hlow : l ∈ fwBridgeLowStock X R) (hhigh : h ∈ fwBridgeHighStock X R) :
    |(((l : ℝ) + (h : ℝ)) / 2) - X / 2| ≤ (23 / 1848 : ℝ) * X := by
  have hg := fw_bridge_window_geometry X R hX hR
  have hl := (mem_apInterval_iff (fwBridgeLowStart X R) (fwBridgeLowEnd X R) 2 1
    (by linarith [hg.2.2.1]) (by linarith [hg.2.2.1, hg.2.2.2.1]) l).mp hlow
  have hh := (mem_apInterval_iff (fwBridgeHighStart X R) (fwBridgeHighEnd X R) 2 1
    (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1])
    (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1]) h).mp hhigh
  have hw : fwBridgeWidth X R ≤ (23 / 924 : ℝ) * X := by
    unfold fwBridgeWidth
    have hs := (bridgeSpan_properties X R hX hR).2.2
    nlinarith
  have hlb := hl.2.1
  have hlu := hl.2.2.1
  have hhb := hh.2.1
  have hhu := hh.2.2.1
  simp only [fwBridgeLowStart, fwBridgeLowEnd, fwBridgeHighStart, fwBridgeHighEnd] at hlb hlu hhb hhu
  apply abs_le.mpr
  constructor <;> linarith

lemma fw_bridge_selected_pair_midpoint_window {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (a : Cell n ≃ Fin (n * n))
    (hdiag : ∀ t side, entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry a (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x))
    (j : Fin 5) (k : Fin (3 * (n + 8))) (p : Fin 2) :
    let q := Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8)) (finProdFinEquiv (k,p))
    |(((entry a (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc ((j,q),false)) : ℝ) +
       (entry a (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc ((j,q),true)) : ℝ)) / 2) -
        (poolMaximum n : ℝ) / 2| ≤ (23 / 1848 : ℝ) * poolMaximum n := by
  dsimp only
  rw [fw_bridge_selected_pair_entry_oriented hrect hs choice rows cols hr hc initial batches hvalid a hdiag hord j k p false,
    fw_bridge_selected_pair_entry_oriented hrect hs choice rows cols hr hc initial batches hvalid a hdiag hord j k p true]
  let X : ℝ := poolMaximum n
  let R := fwBridgeRadius X j
  have hX : 0 < X := by
    change (0 : ℝ) < (poolMaximum n : ℝ)
    exact_mod_cast (poolMaximum_prime n).pos
  have hR : 0 < R := fw_bridge_nominal_radius_pos X hX j j.isLt
  let b := fwBridgeStageBlock n initial batches hvalid j k
  have hv := fwBridgeStageBlock_valid n initial batches hvalid j k
  have h₁ := fw_bridge_window_stock_midpoint X R hX hR b.low₁ b.high₁
    (Finset.mem_sdiff.mp hv.1).1 (Finset.mem_sdiff.mp hv.2.2.1).1
  have h₂ := fw_bridge_window_stock_midpoint X R hX hR b.low₂ b.high₂
    (Finset.mem_sdiff.mp hv.2.1).1 (Finset.mem_sdiff.mp hv.2.2.2.1).1
  fin_cases p
  · simpa [prefixPairCorner, DoublePair.endpoint, b, X] using h₁
  · simpa [prefixPairCorner, DoublePair.endpoint, b, X] using h₂
/-- Every placed bridge pair has the stated absolute deviation from the
actual prescribed-pool mean, under the explicit finite theta and RS inputs. -/
theorem fw_bridge_physical_pair_midpoint_bound_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n L : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (a : Cell n ≃ Fin (n * n))
    (hdiag : ∀ t side, entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry a (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x))
    (j : Fin 5) (i : Fin (6 * (n + 8))) :
    |(((entry a (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc ((j,i),false)) : ℝ) +
       (entry a (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc ((j,i),true)) : ℝ)) / 2) -
        centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (6109 / 231000 : ℝ) * (poolMaximum n : ℝ) := by
  let v : Fin (3 * (n + 8)) × Fin 2 := finProdFinEquiv.symm
    (Fin.cast (by omega : 6 * (n + 8) = 3 * (n + 8) * 2) i)
  have hidx : Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
      (finProdFinEquiv v) = i := by
    dsimp [v]
    simp only [Equiv.apply_symm_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
  have hmid := fw_bridge_selected_pair_midpoint_window hrect hs choice rows cols hr hc initial batches hvalid
    a hdiag hord j v.1 v.2
  dsimp only at hmid
  rw [show (v.1, v.2) = v from Prod.eta v, hidx] at hmid
  obtain ⟨hlo, hhi⟩ := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi
  rw [prescribedPoolValues_mean]
  have hmid' := abs_le.mp hmid
  apply abs_le.mpr
  constructor <;> nlinarith [hmid'.1, hmid'.2, hlo, hhi]

end
end Sude
