import Sude.FWSeedLineIncidence

/-! Exact unsquared stage-mean contributions on the actual offset seed slots.
The rectangle terms remain explicit. -/
namespace Sude
noncomputable section

theorem fw_seed_row_stage_mean_split {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (stages : Finset (Fin 16)) (r : Fin n) (mean : Fin 16 → ℝ) :
    (∑ j ∈ stages, mean j * ∑ q : Fin (6 * (n + 8)),
      physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun c => c.1 = r) (j, q)) =
      12 * (∑ j ∈ stages, mean j) +
        ∑ j ∈ stages, mean j * fwSeedRectangleStageLineWeight hseed hs choice (fun c => c.1 = r) j := by
  simp_rw [fw_seed_existing_row_line_weight hseed hs choice sr sc hsr hsc]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

theorem fw_seed_column_stage_mean_split {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (stages : Finset (Fin 16)) (c : Fin n) (mean : Fin 16 → ℝ) :
    (∑ j ∈ stages, mean j * ∑ q : Fin (6 * (n + 8)),
      physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun x => x.2 = c) (j, q)) =
      12 * (∑ j ∈ stages, mean j) +
        ∑ j ∈ stages, mean j * fwSeedRectangleStageLineWeight hseed hs choice (fun x => x.2 = c) j := by
  simp_rw [fw_seed_existing_column_line_weight hseed hs choice sr sc hsr hsc]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

end
end Sude
