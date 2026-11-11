import Sude.CentralExactPool
import Sude.DiagonalFullStockIntegrated

namespace Sude
noncomputable section

/-- The final reservation contains the centered reservation, so its exact
unused-pool cardinality is at most the post-center cardinality. -/
theorem full_stock_final_card_le_center_card {n : ℕ} (b₀ b : Cell n ≃ Fin (n*n))
    (reserved : Finset (Cell n)) (hn : 0 < n) (hodd : Odd n)
    (hcenter : centralCell n hn ∉ reserved) :
    (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ≤
      (actualUnusedPool b₀ (reserved ∪ {centralCell n hn})).card := by
  classical
  have hc : centralCell n hn ∈ unreservedDiagonalCells reserved := by
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_union_left _ (centerCell_on_both_diagonals n hn hodd).1, hcenter⟩
  have hsub : reserved ∪ {centralCell n hn} ⊆ reserved ∪ unreservedDiagonalCells reserved := by
    intro z hz
    rcases Finset.mem_union.mp hz with hr | hc'
    · exact Finset.mem_union_left _ hr
    · have hz : z = centralCell n hn := Finset.mem_singleton.mp hc'
      exact Finset.mem_union_right _ (hz ▸ hc)
  have hcard := Finset.card_le_card hsub
  have h₀ := actualUnusedPool_card n b₀ (reserved ∪ {centralCell n hn})
  have h₁ := actualUnusedPool_card n b (reserved ∪ unreservedDiagonalCells reserved)
  omega

/-- Bound the two actual denominators by the geometric stock lower bound. -/
theorem full_stock_post_mean_shift_explicit {n : ℕ} (a b₀ b : Cell n ≃ Fin (n*n))
    (reserved : Finset (Cell n)) (hn : 7 ≤ n) (hodd : Odd n)
    (hcenter : centralCell n (by omega) ∉ reserved)
    (hfinal : 2*n ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card)
    (hshift : |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
      (poolMaximum n : ℝ) / (2 * (actualUnusedPool b₀ (reserved ∪ {centralCell n (by omega)})).card) +
        (poolMaximum n : ℝ) / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card) :
    2*n ≤ (actualUnusedPool b₀ (reserved ∪ {centralCell n (by omega)})).card ∧
    |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
      (3 * (poolMaximum n : ℝ)) / (4 * n) := by
  let centerN := (actualUnusedPool b₀ (reserved ∪ {centralCell n (by omega)})).card
  let finalN := (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card
  have hN : finalN ≤ centerN := full_stock_final_card_le_center_card b₀ b reserved (by omega) hodd hcenter
  have hN0 : 2*n ≤ centerN := le_trans hfinal hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hX : (0 : ℝ) ≤ poolMaximum n := by positivity
  have hcenterR : 2*(n : ℝ) ≤ centerN := by exact_mod_cast hN0
  have hfinalR : 2*(n : ℝ) ≤ finalN := by exact_mod_cast hfinal
  have hc : (poolMaximum n : ℝ) / (2 * centerN) ≤ (poolMaximum n : ℝ) / (4*n) := by
    apply div_le_div_of_nonneg_left hX (by positivity)
    linarith
  have hf : (poolMaximum n : ℝ) / finalN ≤ (poolMaximum n : ℝ) / (2*n) := by
    apply div_le_div_of_nonneg_left hX (by positivity)
    exact hfinalR
  have hs : (poolMaximum n : ℝ)/(4*n) + (poolMaximum n : ℝ)/(2*n) =
      3*(poolMaximum n : ℝ)/(4*n) := by ring
  refine ⟨hN0, ?_⟩
  dsimp only [centerN, finalN] at hc hf
  linarith

/-- One integrated physical witness has the explicit mean displacement
bound, alongside the same diagonal, line and remaining-stock conclusions. -/
theorem odd_full_stock_integrated_witness_explicit_mean {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (reserved : Finset (Cell n)) (hn7 : 7 ≤ n) (hodd : Odd n)
    (hcenter : centralCell n (by omega) ∉ reserved)
    (hreserve : 4 * reserved.card ≤ n*n) :
    ∃ b₀ b : Cell n ≃ Fin (n*n), (∀ z ∈ reserved, entry b₀ z = entry a z) ∧ (∀ z ∈ reserved, entry b z = entry a z) ∧
      |(mainSum b : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((mainCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (poolMaximum n : ℝ) ∧
      |(antiSum b : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((antiCells n \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (3/2 : ℝ) * poolMaximum n ∧
      2*n ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
        (3 * (poolMaximum n : ℝ)) / (4 * n) ∧
      ∀ line : Finset (Cell n), line.card ≤ n → (line ∩ unreservedDiagonalCells reserved).card ≤ 2 →
        |((∑ z ∈ line ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
            ((line \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) *
              centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue) -
          ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
            ((line \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          3 * (poolMaximum n : ℝ) := by
  obtain ⟨b₀, b, hfixed₀, hfixed, hmain, hanti, hstock, hmean, hlines⟩ :=
    odd_full_stock_integrated_diagonal_witness_with_mean a reserved hn7 hodd hcenter hreserve
  have hexp := full_stock_post_mean_shift_explicit a b₀ b reserved hn7 hodd hcenter hstock hmean
  exact ⟨b₀, b, hfixed₀, hfixed, hmain, hanti, hstock, hexp.2, hlines⟩

end
end Sude
