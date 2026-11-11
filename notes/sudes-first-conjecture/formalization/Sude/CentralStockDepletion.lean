import Sude.CentralStockCount

/-! Allocation-specific charging for the bounded central stock. -/
namespace Sude
noncomputable section

/-- The two outer bands are separated from the central interval when the
mean displacement, central radius and band width fit inside the quarter-gap. -/
theorem central_window_avoids_outer_bands (X m μ σ ε w u : ℝ)
    (hX : 0 < X) (hmean : |μ - m| ≤ σ * X)
    (hgap : σ + ε + w < 1 / 4)
    (hu : u ≤ m - X / 4 + w * X ∨ m + X / 4 - w * X ≤ u) :
    ¬ (μ - ε * X < u ∧ u ≤ μ + ε * X) := by
  have hsep : 0 < (1 / 4 - σ - ε - w) * X := mul_pos (by linarith) hX
  have hm := abs_le.mp hmean
  intro hwindow
  rcases hu with hu | hu <;> nlinarith

/-- Reservations covered by `accounted ∪ shielded` lose at most the
accounted values in an interval, provided the shielded values miss it. -/
theorem interval_deletions_le_accounted (lo hi : ℝ) (deleted accounted shielded : Finset ℕ)
    (hcover : deleted ⊆ accounted ∪ shielded)
    (hprotect : ∀ p ∈ shielded, p ∉ apInterval lo hi 2 1) :
    (apInterval lo hi 2 1 ∩ deleted).card ≤ accounted.card := by
  apply Finset.card_le_card
  intro p hp
  have hinterval := (Finset.mem_inter.mp hp).1
  have hdeleted := (Finset.mem_inter.mp hp).2
  rcases Finset.mem_union.mp (hcover hdeleted) with h | h
  · exact h
  · exact (hprotect p h hinterval).elim

/-- All available interval values in a central window are actual unused
pool entries in the central stock. -/
theorem available_central_interval_le_stock {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (radius : ℝ) (hradius : 0 ≤ radius)
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - radius)
    (hright : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + radius ≤ poolMaximum n) :
    let μ := centralEntriesMean (actualUnusedPool a reserved) centralPoolValue
    let deleted := reserved.image (entry a)
    (availableInterval (μ - radius) (μ + radius) 2 1 deleted).card ≤
      (centralExceptionStock a reserved radius).card := by
  classical
  dsimp only
  let μ := centralEntriesMean (actualUnusedPool a reserved) centralPoolValue
  let lo := μ - radius
  let hi := μ + radius
  let deleted := reserved.image (entry a)
  have hbc : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hsub : availableInterval lo hi 2 1 deleted ⊆
      (centralExceptionStock a reserved radius).image Subtype.val := by
    intro p hp
    have hm := Finset.mem_sdiff.mp hp
    have hp_pool := even_apInterval_subset_pool n lo hi 2 1
      (by linarith [hleft]) (by linarith [hleft, hbc]) hright (by decide) (by decide) p hm.1
    let v : pool n := ⟨p, hp_pool⟩
    have hv : v ∈ actualUnusedPool a reserved := by
      apply (mem_actualUnusedPool a reserved v).2
      intro z hz heq
      apply hm.2
      exact Finset.mem_image.mpr ⟨z, hz, heq.symm⟩
    have hint := (mem_apInterval_iff lo hi 2 1 (by linarith [hleft]) (by linarith [hleft, hbc]) p).mp hm.1
    have hnear : |centralPoolValue v - μ| ≤ radius := by
      rw [abs_le]
      dsimp [centralPoolValue, v, lo, hi] at hint ⊢
      constructor <;> linarith [hint.2.1, hint.2.2.1]
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hnear⟩, rfl⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcard
  exact hcard

/-- BMOR central stock with an explicit bound on only the reserved values
that actually lie in the central interval. -/
theorem bmor_central_stock_charged_deletions (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (ε : ℝ) (D : ℕ) (hε : 0 ≤ ε)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n)
    (hright : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n ≤
      poolMaximum n)
    (hdeleted :
      (apInterval (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n)
        (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n) 2 1 ∩
          reserved.image (entry a)).card ≤ D) :
    centralStockFullReservationBound a reserved ε + reserved.card - D ≤
      (centralExceptionStock a reserved (ε * poolMaximum n)).card := by
  classical
  let μ := centralEntriesMean (actualUnusedPool a reserved) centralPoolValue
  let X : ℝ := poolMaximum n
  let lo := μ - ε * X
  let hi := μ + ε * X
  let deleted := reserved.image (entry a)
  have hrad : 0 ≤ ε * X := mul_nonneg hε (by dsimp [X]; positivity)
  have hbc : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hs := bmor_two_pool_interval_supply bmor upper n lo hi hn hnmax hleft hbc hright
  have hsum := Finset.card_sdiff_add_card_inter (apInterval lo hi 2 1) deleted
  have hsum' : (availableInterval lo hi 2 1 deleted).card +
      (apInterval lo hi 2 1 ∩ deleted).card = (apInterval lo hi 2 1).card := hsum
  have hsumR : ((availableInterval lo hi 2 1 deleted).card : ℝ) +
      (apInterval lo hi 2 1 ∩ deleted).card = (apInterval lo hi 2 1).card := by exact_mod_cast hsum'
  have hdelR : ((apInterval lo hi 2 1 ∩ deleted).card : ℝ) ≤ D := by exact_mod_cast hdeleted
  have hstock := available_central_interval_le_stock a reserved (ε * X) hrad hleft hright
  have hstockR : ((availableInterval lo hi 2 1 deleted).card : ℝ) ≤
      (centralExceptionStock a reserved (ε * X)).card := by exact_mod_cast hstock
  have heq : hi - lo = 2 * (ε * X) := by dsimp [hi, lo]; ring
  rw [heq] at hs
  change (2 * (ε * X) - (518 / 125 : ℝ) * (Real.sqrt lo + Real.sqrt hi)) /
      Real.log X - (reserved.card : ℝ) + reserved.card - D ≤ _
  linarith [hs.1]

/-- Source-style deletion accounting: entries in the two outer bands are
shown to miss the central interval and are not charged against `D`.
The supplied cover must account for every reserved value. -/
theorem bmor_central_stock_excluding_outer_bands (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (accounted shielded : Finset ℕ) (D : ℕ)
    (m σ ε w : ℝ) (hε : 0 ≤ ε) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n)
    (hright : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n ≤
      poolMaximum n)
    (hmean : |centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - m| ≤ σ * poolMaximum n)
    (hgap : σ + ε + w < 1 / 4)
    (hcover : reserved.image (entry a) ⊆ accounted ∪ shielded)
    (haccount : accounted.card ≤ D)
    (hband : ∀ p ∈ shielded, (p : ℝ) ≤ m - (poolMaximum n : ℝ) / 4 + w * poolMaximum n ∨
      m + (poolMaximum n : ℝ) / 4 - w * poolMaximum n ≤ p) :
    centralStockFullReservationBound a reserved ε + reserved.card - D ≤
      (centralExceptionStock a reserved (ε * poolMaximum n)).card := by
  let μ := centralEntriesMean (actualUnusedPool a reserved) centralPoolValue
  let X : ℝ := poolMaximum n
  let lo := μ - ε * X
  let hi := μ + ε * X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hrad : 0 ≤ ε * X := mul_nonneg hε hX.le
  have hbc : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hprotect : ∀ p ∈ shielded, p ∉ apInterval lo hi 2 1 := by
    intro p hp hpi
    have hmem := (mem_apInterval_iff lo hi 2 1 (by linarith [hleft]) (by linarith [hleft, hbc]) p).mp hpi
    have haway := central_window_avoids_outer_bands X m μ σ ε w p hX hmean hgap (hband p hp)
    exact haway ⟨hmem.2.1, hmem.2.2.1⟩
  have hdel := (interval_deletions_le_accounted lo hi (reserved.image (entry a)) accounted shielded
    hcover hprotect).trans haccount
  exact bmor_central_stock_charged_deletions bmor upper a reserved ε D hε hn hnmax hleft hright hdel

/-- RF10's simpler square-root enclosure is below the endpoint-specific
BMOR bound. The logarithm is natural and its denominator is positive. -/
theorem central_source_bound_le_charged {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (ε : ℝ) (D : ℕ) (hε : 0 ≤ ε)
    (hright : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n ≤
      poolMaximum n) :
    (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - D ≤
      centralStockFullReservationBound a reserved ε + reserved.card - D := by
  let μ := centralEntriesMean (actualUnusedPool a reserved) centralPoolValue
  let X : ℝ := poolMaximum n
  have hX : (1 : ℝ) < X := by
    dsimp [X]
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (poolMaximum_prime n).two_le)
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hrad : 0 ≤ ε * X := mul_nonneg hε (le_of_lt (by linarith : 0 < X))
  have hlo : μ - ε * X ≤ X := by linarith [hright]
  have hhi : μ + ε * X ≤ X := hright
  have hslo := Real.sqrt_le_sqrt hlo
  have hshi := Real.sqrt_le_sqrt hhi
  have hnum : 2 * (ε * X) - (1036 / 125 : ℝ) * Real.sqrt X ≤
      2 * (ε * X) - (518 / 125 : ℝ) * (Real.sqrt (μ - ε * X) + Real.sqrt (μ + ε * X)) := by
    linarith
  have hdiv := div_le_div_of_nonneg_right hnum hlog.le
  change (2 * (ε * X) - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X - D ≤
    (2 * (ε * X) - (518 / 125 : ℝ) * (Real.sqrt (μ - ε * X) + Real.sqrt (μ + ε * X))) /
      Real.log X - (reserved.card : ℝ) + reserved.card - D
  linarith

/-- RF10's count for actual unused pool entries, under the published BMOR
and RS hypotheses and an explicit charged-deletion bound. -/
theorem bmor_central_stock_source_bound (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (ε : ℝ) (D : ℕ) (hε : 0 ≤ ε)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n)
    (hright : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n ≤
      poolMaximum n)
    (hdeleted :
      (apInterval (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n)
        (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n) 2 1 ∩
          reserved.image (entry a)).card ≤ D) :
    (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - D ≤
      (centralExceptionStock a reserved (ε * poolMaximum n)).card :=
  (central_source_bound_le_charged a reserved ε D hε hright).trans
    (bmor_central_stock_charged_deletions bmor upper a reserved ε D hε hn hnmax hleft hright hdeleted)

/-- Compose RF10's charged stock bound with the physical RF3 completion.
The charged-deletion condition and numerical gate are explicit, not imports. -/
theorem bmor_balanced_charged_completion (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) {n r₀ b : ℕ}
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (hmain : mainCells n ⊆ reserved) (hanti : antiCells n ⊆ reserved)
    (hload : 4 * (r₀ + 6 * b + 4) ≤ n)
    (hrowlo : ∀ i, r₀ ≤ (LayerPacking.rowUsed reserved i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed reserved i).card ≤ r₀ + (6 * b + 4))
    (hcollo : ∀ i, r₀ ≤ (LayerPacking.colUsed reserved i).card)
    (hcolhi : ∀ i, (LayerPacking.colUsed reserved i).card ≤ r₀ + (6 * b + 4))
    (ε : ℝ) (D : ℕ) (hε : 0 ≤ ε) (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n)
    (hright : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n ≤
      poolMaximum n)
    (hdeleted :
      (apInterval (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - ε * poolMaximum n)
        (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue + ε * poolMaximum n) 2 1 ∩
          reserved.image (entry a)).card ≤ D)
    (hgate : (((9 * b + 6) * n : ℕ) : ℝ) ≤
      (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - D) :
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
  have hs := bmor_central_stock_source_bound bmor upper a reserved ε D hε hn hnmax hleft hright hdeleted
  have hcountR : (((9 * b + 6) * n : ℕ) : ℝ) ≤
      (centralExceptionStock a reserved (ε * poolMaximum n)).card := hgate.trans hs
  have hcount : (9 * b + 6) * n ≤
      (centralExceptionStock a reserved (ε * poolMaximum n)).card := by exact_mod_cast hcountR
  exact balanced_residual_central_completion a reserved hmain hanti hload hrowlo hrowhi hcollo hcolhi
    ε hε hcount

end
end Sude
