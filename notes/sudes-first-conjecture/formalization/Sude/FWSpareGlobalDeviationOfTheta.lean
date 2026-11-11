import Sude.FWRoleCellOccupancy
import Sude.FWPhysicalPrefixMeanOfTheta
import Sude.ReservedPoolMean

/-! Actual full-reservation spare-cell deviation from the prescribed-pool
mean, conditional on the finite-theta and RS inputs. No line, diagonal, or
theta-witness-existence conclusion is asserted. -/
namespace Sude
noncomputable section

/-- The actual entries in `full \ roles`, each charged once, have global
centered sum bounded by `257X/500` times their exact FW spare-cell count. -/
theorem fw_spare_global_deviation_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n P : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice)
      (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (a : Cell n ≃ Fin (n * n)) :
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let D : ℝ := (∑ c ∈ full \ roles, (entry a c : ℝ)) - ((full \ roles).card : ℝ) * μ
    |D| ≤ (257 / 500 : ℝ) * (poolMaximum n : ℝ) * ((96 * (238 - P) : ℕ) : ℝ) := by
  classical
  dsimp only
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
  let μ : ℝ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  have hocc := fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have hcard : (full \ roles).card = 96 * (238 - P) := hocc.2.2.2.2.2.1
  obtain ⟨hlo, hhi⟩ := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi
  rw [← prescribedPoolValues_mean] at hlo hhi
  have hterm : ∀ c ∈ full \ roles, |(entry a c : ℝ) - μ| ≤
      (257 / 500 : ℝ) * (poolMaximum n : ℝ) := by
    intro c hc
    obtain ⟨hl, hu⟩ := physical_entry_pool_range a c
    apply abs_le.mpr
    constructor <;> linarith
  have hcenter : (∑ c ∈ full \ roles, (entry a c : ℝ)) - ((full \ roles).card : ℝ) * μ =
      ∑ c ∈ full \ roles, ((entry a c : ℝ) - μ) := by
    simp [Finset.sum_sub_distrib, nsmul_eq_mul]
  change |(∑ c ∈ full \ roles, (entry a c : ℝ)) - ((full \ roles).card : ℝ) * μ| ≤ _
  rw [hcenter]
  calc
    |∑ c ∈ full \ roles, ((entry a c : ℝ) - μ)| ≤
        ∑ c ∈ full \ roles, |(entry a c : ℝ) - μ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ full \ roles, (257 / 500 : ℝ) * (poolMaximum n : ℝ) := Finset.sum_le_sum hterm
    _ = (257 / 500 : ℝ) * (poolMaximum n : ℝ) * ((96 * (238 - P) : ℕ) : ℝ) := by
      simp [hcard, nsmul_eq_mul, mul_comm]

end
end Sude
