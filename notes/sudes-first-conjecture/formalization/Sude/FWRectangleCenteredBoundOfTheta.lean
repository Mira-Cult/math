import Sude.PackedRectangleCenteredLineBound
import Sude.FWPhysicalPrefixMeanOfTheta

/-! The full packed-rectangle contribution around the actual prescribed-pool
mean, conditional on the stated finite-theta and RS inputs. No role-unused
mean, diagonal, full-line, or witness-existence conclusion is asserted. -/
namespace Sude
noncomputable section

/-- On the stated FW order interval, the actual pool mean and entry bounds
give one `257X/250` centered charge for the whole supplied packed-rectangle
support on each row and column. -/
theorem fw_packed_rectangle_centered_bound_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {L n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n)) :
    (∀ r : Fin n,
      (LayerPacking.rowUsed (packedRectangleSupport hs choice) r).card ≤ 2 ∧
      |∑ c ∈ LayerPacking.rowUsed (packedRectangleSupport hs choice) r,
        ((entry a (r, c) : ℝ) - (Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ))| ≤
          (257 / 250 : ℝ) * (poolMaximum n : ℝ)) ∧
    (∀ c : Fin n,
      (LayerPacking.colUsed (packedRectangleSupport hs choice) c).card ≤ 2 ∧
      |∑ r ∈ LayerPacking.colUsed (packedRectangleSupport hs choice) c,
        ((entry a (r, c) : ℝ) - (Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ))| ≤
          (257 / 250 : ℝ) * (poolMaximum n : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi
  exact packed_rectangle_centered_row_column_bound hs choice a (poolMaximum n : ℝ)
    ((Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ)) (Nat.cast_nonneg _)
    (physical_entry_pool_range a) hlo hhi

end
end Sude
