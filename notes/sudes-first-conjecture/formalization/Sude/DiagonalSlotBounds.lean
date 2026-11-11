import Sude.DiagonalPhysicalInvoice

/-! Width-weighted bounds for actual diagonal pair slots. -/
namespace Sude
noncomputable section

/-- The actual main-diagonal slots cost at most the common source invoice. -/
theorem physicalMainSlot_weighted_invoice {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (otherChoice : Fin L → Bool) (width : Fin P → ℝ) (z : ℝ) :
    (∑ j, (width j) ^ 2 * ∑ q ∈ physicalPrefixSlots hfit hdiag,
      (physicalDiagonalSlotWeight hfit hdiag hrect hs (bridgeDiagonalChoice hrect otherChoice)
        (fun c => c ∈ mainCells n) j q) ^ 2) ≤
      3 * (d : ℝ) * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
  simp_rw [physicalDiagonalSlotWeight_sq_sum,
    prefixRectangle_main_stage_invoice hrect hs hL otherChoice]
  have hsum : 0 ≤ ∑ j, (width j) ^ 2 := Finset.sum_nonneg (by intro j _; exact sq_nonneg _)
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  rw [← Finset.sum_mul]
  nlinarith [mul_nonneg hd hsum, sq_nonneg z]

/-- The actual antidiagonal slots obey the same bound. -/
theorem physicalAntiSlot_weighted_invoice {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (otherChoice : Fin L → Bool) (width : Fin P → ℝ) (z : ℝ) :
    (∑ j, (width j) ^ 2 * ∑ q ∈ physicalPrefixSlots hfit hdiag,
      (physicalDiagonalSlotWeight hfit hdiag hrect hs (bridgeDiagonalChoice hrect otherChoice)
        (fun c => c ∈ antiCells n) j q) ^ 2) ≤
      3 * (d : ℝ) * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
  simp_rw [physicalDiagonalSlotWeight_sq_sum,
    prefixRectangle_anti_stage_invoice hrect hs hL otherChoice]
  have hsum : 0 ≤ ∑ j, (width j) ^ 2 := Finset.sum_nonneg (by intro j _; exact sq_nonneg _)
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  rw [← Finset.sum_mul]
  nlinarith [mul_nonneg hd hsum, sq_nonneg z]

end
end Sude
