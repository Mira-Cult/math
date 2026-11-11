import Sude.CYFullKeepoutFactorCount
import Sude.CentralConstruct
import Sude.PoolWidth
namespace Sude
noncomputable section

/-- The CY factor on the full keepout gives conditional central-stock completion.
The post-diagonal stock premise is explicit and is not supplied analytically here. -/
theorem cy_full_keepout_central_completion {L n : ℕ}
    (hs : 2*L+1 ≤ n) (hL : 3 ≤ L) (hn : 7 ≤ n) (hodd : Odd n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (hload : 4*(2*(rows.length+cols.length)+4) ≤ n)
    (a : Cell n ≃ Fin (n*n)) (ε : ℝ) (hε : 0 ≤ ε)
    (hstock : let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
      let final := full ∪ unreservedDiagonalCells full
      3*n+1 ≤ (centralExceptionStock a final (ε * poolMaximum n)).card) :
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    let final := full ∪ unreservedDiagonalCells full
    ∃ b : Cell n ≃ Fin (n*n), (∀ z ∈ final, entry b z = entry a z) ∧
      (∀ i, |(rowSum b i : ℝ) - ((∑ z ∈ rowCells i ∩ final, (entry a z : ℝ)) +
        ((rowCells i \ final).card : ℝ) * centralEntriesMean (actualUnusedPool a final) centralPoolValue)| <
        (1+8*ε) * poolMaximum n) ∧
      (∀ i, |(columnSum b i : ℝ) - ((∑ z ∈ columnCells i ∩ final, (entry a z : ℝ)) +
        ((columnCells i \ final).card : ℝ) * centralEntriesMean (actualUnusedPool a final) centralPoolValue)| <
        (1+8*ε) * poolMaximum n) ∧
      mainSum b = mainSum a ∧ antiSum b = antiSum a ∧ Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  dsimp only at hstock ⊢
  let ρ := 2*(rows.length+cols.length)
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  let final := full ∪ unreservedDiagonalCells full
  let E := (Finset.univ : Finset (Cell n)) \ final
  have hg := cy_full_keepout_factor_and_total hs hL hn hodd choice rows cols hrows hcols hload
  change ∃ F ⊆ E, CellFactorRegular F (n-ρ-5) ∧
      (∀ x, (rowCells x ∩ (E \ F)).card ≤ 4) ∧
      (∀ x, (columnCells x ∩ (E \ F)).card ≤ 4) ∧
      (E \ F).card + 3*L = 3*n+1 ∧ (E \ F).card ≤ 3*n+1 at hg
  obtain ⟨F,hFE,hreg,hrow,hcol,_,hcount⟩ := hg
  have hk : 0 < n-ρ-5 := by dsimp [ρ] at *; omega
  have hdiag := postDiagonal_contains_both full
  have hrad : 0 ≤ ε * (poolMaximum n : ℝ) := mul_nonneg hε (by positivity)
  have hs' : (E \ F).card ≤ (centralExceptionStock a final (ε * poolMaximum n)).card := hcount.trans hstock
  have hc := central_stock_regular_factor_completion (k := n-ρ-5) (t := 4) a final F
    hFE hreg hk (by omega) hdiag.1 hdiag.2 (poolMaximum n) (ε * poolMaximum n) hrad
    (actual_unused_pool_strict_width a final) hs' hrow hcol
  have heq : (poolMaximum n : ℝ) + 2 * (4 : ℕ) * (ε * poolMaximum n) =
      (1 + 8 * ε) * poolMaximum n := by ring
  simpa only [heq] using hc
end
end Sude
