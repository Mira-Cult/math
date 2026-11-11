import Sude.FWSeedRectangleLineCounts

/-! Exact ordinary incidence alternatives for actual seed stage slots. -/
namespace Sude
noncomputable section

theorem fw_seed_existing_row_line_weight_twelve_or_fourteen {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (r : Fin n) :
    (∑ q : Fin (6 * (n + 8)),
      physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun c => c.1 = r) (j, q)) = 12 ∨
    (∑ q : Fin (6 * (n + 8)),
      physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun c => c.1 = r) (j, q)) = 14 := by
  classical
  have h := fw_seed_existing_row_line_weight hseed hs choice sr sc hsr hsc j r
  rw [fw_seed_rectangle_row_stage_weight hseed hs choice j r] at h
  split_ifs at h <;> norm_num at h <;> simp_all

theorem fw_seed_existing_column_line_weight_twelve_or_fourteen {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (c : Fin n) :
    (∑ q : Fin (6 * (n + 8)),
      physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun x => x.2 = c) (j, q)) = 12 ∨
    (∑ q : Fin (6 * (n + 8)),
      physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun x => x.2 = c) (j, q)) = 14 := by
  classical
  have h := fw_seed_existing_column_line_weight hseed hs choice sr sc hsr hsc j c
  rw [fw_seed_rectangle_column_stage_weight hseed hs choice j c] at h
  split_ifs at h <;> norm_num at h <;> simp_all

end
end Sude
