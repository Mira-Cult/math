import Sude.CYFullKeepoutFactorCount
import Sude.CentralConstruct
import Sude.RegularFactorExactExceptionCompletion

/-! CY completion using exact global exception and local incidence counts. -/
namespace Sude
noncomputable section

theorem cy_full_keepout_sharp_central_completion {L n : ℕ}
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
    ∃ b : Cell n ≃ Fin (n*n),
      (∀ z ∈ final, entry b z = entry a z) ∧
      (∀ i, |(rowSum b i : ℝ) - ((∑ z ∈ rowCells i ∩ final, (entry a z : ℝ)) +
        ((rowCells i \ final).card : ℝ) * centralEntriesMean (actualUnusedPool a final) centralPoolValue)| <
          (1 + (7 + 1/(n : ℝ))*ε) * poolMaximum n) ∧
      (∀ i, |(columnSum b i : ℝ) - ((∑ z ∈ columnCells i ∩ final, (entry a z : ℝ)) +
        ((columnCells i \ final).card : ℝ) * centralEntriesMean (actualUnusedPool a final) centralPoolValue)| <
          (1 + (7 + 1/(n : ℝ))*ε) * poolMaximum n) ∧
      mainSum b = mainSum a ∧ antiSum b = antiSum a ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  dsimp only at hstock ⊢
  let ρ := 2*(rows.length+cols.length)
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  let final := full ∪ unreservedDiagonalCells full
  let E := (Finset.univ : Finset (Cell n)) \ final
  have hfac := cy_full_keepout_factor_and_total hs hL hn hodd choice rows cols hrows hcols hload
  change ∃ F ⊆ E, CellFactorRegular F (n-ρ-5) ∧
    (∀ x, (rowCells x ∩ (E \ F)).card ≤ 4) ∧
    (∀ x, (columnCells x ∩ (E \ F)).card ≤ 4) ∧
    (E \ F).card + 3*L = 3*n+1 ∧ (E \ F).card ≤ 3*n+1 at hfac
  obtain ⟨F,hFE,hreg,hrow,hcol,_,hcard⟩ := hfac
  have hk : 0 < n-ρ-5 := by dsimp [ρ] at *; omega
  have hdiags := postDiagonal_contains_both full
  have hrad : 0 ≤ ε * (poolMaximum n : ℝ) := mul_nonneg hε (by positivity)
  have hcount : (E \ F).card ≤ (centralExceptionStock a final (ε * poolMaximum n)).card := by
    exact hcard.trans hstock
  have h := central_stock_regular_factor_completion_exact_count (k := n-ρ-5) (t := 4) a final F hFE hreg hk
    (by omega) hdiags.1 hdiags.2 (poolMaximum n) (ε * poolMaximum n) hrad
    (actual_unused_pool_strict_width a final) hcount hrow hcol
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hcardR : ((E \ F).card : ℝ) ≤ 3*(n : ℝ)+1 := by exact_mod_cast hcard
  have hfrac : (((E \ F).card : ℝ) / n) ≤ 3 + 1/(n : ℝ) := by
    apply (div_le_iff₀ hnR).2
    field_simp
    nlinarith
  have hXε : 0 ≤ ε * (poolMaximum n : ℝ) := hrad
  have hb : (poolMaximum n : ℝ) + (4 + (((E \ F).card : ℝ) / n)) * (ε * poolMaximum n) ≤
      (1 + (7 + 1/(n : ℝ))*ε) * poolMaximum n := by
    have hc := mul_le_mul_of_nonneg_right hfrac hXε
    nlinarith
  obtain ⟨b,hfixed,hrows,hcols,hmain,hanti,hpool,hinj⟩ := h
  exact ⟨b,hfixed,fun i => lt_of_lt_of_le (hrows i) hb,fun i => lt_of_lt_of_le (hcols i) hb,
    hmain,hanti,hpool,hinj⟩

end
end Sude
