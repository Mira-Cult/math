import Sude.CYFullKeepoutSharpCompletion
import Sude.DiagonalFullStockIntervalShift
import Sude.DiagonalFullStockExplicitMean
import Sude.FWPostDiagonalCompletionGeometry
namespace Sude
noncomputable section

/-- DQ and CY completion for one physical full keepout, conditional on an
old widened-reservation deletion bound and the explicit 3n+1 stock gate. -/
theorem cy_dq_sharp_completion_from_widened_old (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L) (hn : 7 ≤ n) (hnmax : n ≤ 2^18)
    (hodd : Odd n) (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (hload : 4*(2*(rows.length+cols.length)+4) ≤ n)
    (a : Cell n ≃ Fin (n*n)) (ε : ℝ) (Dold : ℕ) (hε : 0 ≤ ε)
    (hreserve : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      4*full.card ≤ n*n)
    (hleft : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      1 ≤ centralEntriesMean (actualUnusedPool a full) centralPoolValue - ε * poolMaximum n - 3*(poolMaximum n : ℝ)/(4*n))
    (hright : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      centralEntriesMean (actualUnusedPool a full) centralPoolValue + ε * poolMaximum n + 3*(poolMaximum n : ℝ)/(4*n) ≤ poolMaximum n)
    (hdeleted : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      (apInterval
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue - ε * poolMaximum n - 3*(poolMaximum n : ℝ)/(4*n))
        (centralEntriesMean (actualUnusedPool a full) centralPoolValue + ε * poolMaximum n + 3*(poolMaximum n : ℝ)/(4*n))
        2 1 ∩ full.image (entry a)).card ≤ Dold)
    (hgate : ((3*n+1 : ℕ) : ℝ) ≤
      (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - (((Dold + (2*n-1) : ℕ)) : ℝ)) :
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    let final := full ∪ unreservedDiagonalCells full
    ∃ b c : Cell n ≃ Fin (n*n),
      (∀ z ∈ full, entry b z = entry a z) ∧
      (∀ z ∈ final, entry c z = entry b z) ∧
      (∀ z ∈ full, entry c z = entry a z) ∧
      |(mainSum c : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry a z : ℝ)) +
        ((mainCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| ≤ (poolMaximum n : ℝ) ∧
      |(antiSum c : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry a z : ℝ)) +
        ((antiCells n \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| ≤ (3/2 : ℝ)*poolMaximum n ∧
      (∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry a z : ℝ)) +
        ((rowCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*ε)*poolMaximum n) ∧
      (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry a z : ℝ)) +
        ((columnCells i \ full).card : ℝ) * centralEntriesMean (actualUnusedPool a full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*ε)*poolMaximum n) ∧
      mainSum c = mainSum b ∧ antiSum c = antiSum b ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) := by
  classical
  dsimp only at hreserve hleft hright hdeleted ⊢
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  let final := full ∪ unreservedDiagonalCells full
  let μ₀ := centralEntriesMean (actualUnusedPool a full) centralPoolValue
  let δ : ℝ := 3*(poolMaximum n : ℝ)/(4*n)
  have hcenter : centralCell n (by omega) ∉ full :=
    fw_full_keepout_avoids_center hs (by omega) choice rows cols hrows hcols
  obtain ⟨b₀,b,_,hfixed,hmain,hanti,_,hmean,hline⟩ :=
    odd_full_stock_integrated_witness_explicit_mean a full hn hodd hcenter hreserve
  let μ₁ := centralEntriesMean (actualUnusedPool b final) centralPoolValue
  have hm : |μ₁ - μ₀| ≤ δ := hmean
  have hleftb : 1 ≤ μ₁ - ε * poolMaximum n := by have h := (abs_le.mp hm).1; dsimp [μ₀, δ] at *; linarith
  have hrightb : μ₁ + ε * poolMaximum n ≤ poolMaximum n := by have h := (abs_le.mp hm).2; dsimp [μ₀, δ] at *; linarith
  have hrad : 0 ≤ ε * (poolMaximum n : ℝ) := mul_nonneg hε (by positivity)
  have hdel := post_diagonal_deletions_from_widened_interval a b full μ₀ μ₁ (ε * poolMaximum n) δ
    (by omega) hodd hfixed hrad hm (by dsimp [μ₀,δ] at *; linarith)
  change (apInterval (μ₀ - ε*poolMaximum n - δ) (μ₀ + ε*poolMaximum n + δ) 2 1 ∩ full.image (entry a)).card ≤ Dold at hdeleted
  have hdel' : (apInterval (μ₁ - ε*poolMaximum n) (μ₁ + ε*poolMaximum n) 2 1 ∩ final.image (entry b)).card ≤
      Dold+(2*n-1) := by
    change (apInterval (μ₁ - ε*poolMaximum n) (μ₁ + ε*poolMaximum n) 2 1 ∩ final.image (entry b)).card ≤
      (apInterval (μ₀ - ε*poolMaximum n - δ) (μ₀ + ε*poolMaximum n + δ) 2 1 ∩ full.image (entry a)).card + (2*n-1) at hdel
    omega
  have hstock := bmor_central_stock_source_bound bmor upper b final ε (Dold+(2*n-1)) hε
    (by omega) hnmax hleftb hrightb hdel'
  have hstockR : ((3*n+1 : ℕ) : ℝ) ≤ (centralExceptionStock b final (ε*poolMaximum n)).card := hgate.trans hstock
  have hstockN : 3*n+1 ≤ (centralExceptionStock b final (ε*poolMaximum n)).card := by exact_mod_cast hstockR
  obtain ⟨c,hfixedc,hrowsC,hcolsC,hmainc,hantic,hpool,hinj⟩ :=
    cy_full_keepout_sharp_central_completion hs hL hn hodd choice rows cols hrows hcols hload b ε hε hstockN
  have hB : (1+(7+1/(n : ℝ))*ε)*poolMaximum n + 3*poolMaximum n =
      (4+(7+1/(n : ℝ))*ε)*poolMaximum n := by ring
  refine ⟨b,c,hfixed,hfixedc,?_,?_,?_,?_,?_,hmainc,hantic,hpool,hinj⟩
  · intro z hz; exact (hfixedc z (Finset.mem_union_left _ hz)).trans (hfixed z hz)
  · rw [hmainc]; exact hmain
  · rw [hantic]; exact hanti
  · intro i
    have ht := hline (rowCells i) (by simp [rowCells_card_exact]) (row_unreserved_diagonal_card_le_two full i)
    have hs' := abs_sub_le (rowSum c i : ℝ)
      ((∑ z ∈ rowCells i ∩ final, (entry b z : ℝ)) + ((rowCells i \ final).card : ℝ) * μ₁)
      ((∑ z ∈ rowCells i ∩ full, (entry a z : ℝ)) + ((rowCells i \ full).card : ℝ) * μ₀)
    rw [← hB]
    linarith [hrowsC i]
  · intro i
    have ht := hline (columnCells i) (by simp [columnCells_card_exact]) (column_unreserved_diagonal_card_le_two full i)
    have hs' := abs_sub_le (columnSum c i : ℝ)
      ((∑ z ∈ columnCells i ∩ final, (entry b z : ℝ)) + ((columnCells i \ final).card : ℝ) * μ₁)
      ((∑ z ∈ columnCells i ∩ full, (entry a z : ℝ)) + ((columnCells i \ full).card : ℝ) * μ₀)
    rw [← hB]
    linarith [hcolsC i]
end
end Sude
