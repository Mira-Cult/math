import Sude.BalancedResidualCompletion
import Sude.APInterval

/-! Bounded analytic central-stock supply with the full reservation charged. -/
namespace Sude
noncomputable section

/-- The q=2 BMOR interval count gives actual central stock after charging
all prior reserved values once. This deliberately uses the full reservation
budget; the source's smaller allocation-specific deletion budget is a
separate obligation. -/
theorem bmor_central_stock_full_reservation (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (ε : ℝ) (hε : 0 ≤ ε)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n)
    (hright : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n ≤
      poolMaximum n) :
    ((2 * (ε * poolMaximum n)) - (518 / 125 : ℝ) *
      (Real.sqrt (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n) +
       Real.sqrt (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n))) /
      Real.log (poolMaximum n) - reserved.card ≤
        (centralExceptionStock a reserved (ε * poolMaximum n)).card := by
  classical
  let μ := centralEntriesMean (actualUnusedPool a reserved) centralPoolValue
  let X : ℝ := poolMaximum n
  let lo := μ - ε * X
  let hi := μ + ε * X
  let deleted := reserved.image (entry a)
  have hrad : 0 ≤ ε * X := mul_nonneg hε (by dsimp [X]; positivity)
  have hbc : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hs := bmor_two_available_pool_supply bmor upper n lo hi deleted hn hnmax hleft hbc hright
  have hsub : availableInterval lo hi 2 1 deleted ⊆
      (centralExceptionStock a reserved (ε * X)).image Subtype.val := by
    intro p hp
    have hav := hs.2 p hp
    let v : pool n := ⟨p, hav.1⟩
    have hv : v ∈ actualUnusedPool a reserved := by
      apply (mem_actualUnusedPool a reserved v).2
      intro z hz heq
      apply hav.2
      exact Finset.mem_image.mpr ⟨z, hz, heq.symm⟩
    have hint := (mem_apInterval_iff lo hi 2 1 (by linarith [hleft]) (by linarith [hleft, hbc]) p).mp
      (Finset.mem_sdiff.mp hp).1
    have hnear : |centralPoolValue v - μ| ≤ ε * X := by
      rw [abs_le]
      dsimp [centralPoolValue, v, lo, hi] at hint ⊢
      constructor <;> linarith [hint.2.1, hint.2.2.1]
    refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨hv, hnear⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcard
  have hcardR : ((availableInterval lo hi 2 1 deleted).card : ℝ) ≤
      (centralExceptionStock a reserved (ε * X)).card := by exact_mod_cast hcard
  have hdeleted : deleted.card = reserved.card := by
    exact Finset.card_image_of_injective _ (entry_injective a)
  rw [hdeleted] at hs
  have heq : hi - lo = 2 * (ε * X) := by dsimp [hi, lo]; ring
  rw [heq] at hs
  exact hs.1.trans hcardR

/-- Explicit analytic lower bound with the full reserved-cell deletion cost. -/
def centralStockFullReservationBound {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (ε : ℝ) : ℝ :=
  let μ := centralEntriesMean (actualUnusedPool a reserved) centralPoolValue
  let X : ℝ := poolMaximum n
  (2 * (ε * X) - (518 / 125 : ℝ) * (Real.sqrt (μ - ε * X) + Real.sqrt (μ + ε * X))) /
    Real.log X - reserved.card

/-- Compose the bounded analytic supply with RF3's physical completion.
The explicit gate uses the conservative full reservation budget; its
verification for any controller is not asserted here. -/
theorem bmor_balanced_residual_completion (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) {n r₀ b : ℕ}
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (hmain : mainCells n ⊆ reserved) (hanti : antiCells n ⊆ reserved)
    (hload : 4 * (r₀ + 6 * b + 4) ≤ n)
    (hrowlo : ∀ i, r₀ ≤ (LayerPacking.rowUsed reserved i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed reserved i).card ≤ r₀ + (6 * b + 4))
    (hcollo : ∀ i, r₀ ≤ (LayerPacking.colUsed reserved i).card)
    (hcolhi : ∀ i, (LayerPacking.colUsed reserved i).card ≤ r₀ + (6 * b + 4))
    (ε : ℝ) (hε : 0 ≤ ε) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n)
    (hright : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n ≤
      poolMaximum n)
    (hgate : (((9 * b + 6) * n : ℕ) : ℝ) ≤ centralStockFullReservationBound a reserved ε) :
    ∃ c : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry c z = entry a z) ∧
      (∀ i, |(rowSum c i : ℝ) -
        ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
          ((rowCells i \ reserved).card : ℝ) *
            centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9 * b + 6 : ℕ) * ε) * poolMaximum n) ∧
      (∀ i, |(columnSum c i : ℝ) -
        ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
          ((columnCells i \ reserved).card : ℝ) *
            centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
          (1 + 2 * (9 * b + 6 : ℕ) * ε) * poolMaximum n) ∧
      mainSum c = mainSum a ∧ antiSum c = antiSum a ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) := by
  have hs := bmor_central_stock_full_reservation bmor upper a reserved ε hε hn hnmax hleft hright
  change centralStockFullReservationBound a reserved ε ≤ _ at hs
  have hcountR : (((9 * b + 6) * n : ℕ) : ℝ) ≤
      (centralExceptionStock a reserved (ε * poolMaximum n)).card := hgate.trans hs
  have hcount : (9 * b + 6) * n ≤
      (centralExceptionStock a reserved (ε * poolMaximum n)).card := by exact_mod_cast hcountR
  exact balanced_residual_central_completion a reserved hmain hanti hload hrowlo hrowhi hcollo hcolhi
    ε hε hcount

end
end Sude
