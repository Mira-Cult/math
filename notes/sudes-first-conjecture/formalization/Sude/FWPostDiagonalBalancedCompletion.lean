import Sude.FWPostDiagonalCompletionGeometry
import Sude.BalancedResidualCompletion

/-! Conditional balanced completion on the same post-diagonal FW keepout.
The post-placement stock bound is explicit; this does not place the diagonals
or assert that their sums are prime. -/
namespace Sude
noncomputable section

/-- Complete the supplied post-diagonal placement while fixing its entire
FW keepout and both diagonals. All pool means and the stock premise refer to
the same supplied placement and enlarged keepout. -/
theorem fw_post_diagonal_balanced_completion {n P : ℕ}
    (hn : 19485 ≤ n) (hnhi : n ≤ 21248) (hP : P ≤ 238)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (hbc : bc.length = 5 * 3) (hsc : sc.length = 16 * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice)
      (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (a : Cell n ≃ Fin (n * n)) (ε : ℝ) (hε : 0 ≤ ε)
    (hstock : let full := packedRectangleSupport hs choice ∪
      LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
      let final := full ∪ unreservedDiagonalCells full
      6 * n ≤ (centralExceptionStock a final (ε * poolMaximum n)).card) :
    let full := packedRectangleSupport hs choice ∪
      LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let final := full ∪ unreservedDiagonalCells full
    ∃ c : Cell n ≃ Fin (n * n),
      (∀ z ∈ final, entry c z = entry a z) ∧
      (∀ i, |(rowSum c i : ℝ) -
        ((∑ z ∈ rowCells i ∩ final, (entry a z : ℝ)) +
          ((rowCells i \ final).card : ℝ) *
            centralEntriesMean (actualUnusedPool a final) centralPoolValue)| <
          (1 + 12 * ε) * poolMaximum n) ∧
      (∀ i, |(columnSum c i : ℝ) -
        ((∑ z ∈ columnCells i ∩ final, (entry a z : ℝ)) +
          ((columnCells i \ final).card : ℝ) *
            centralEntriesMean (actualUnusedPool a final) centralPoolValue)| <
          (1 + 12 * ε) * poolMaximum n) ∧
      mainSum c = mainSum a ∧ antiSum c = antiSum a ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) := by
  classical
  dsimp only at hstock ⊢
  have hg := fw_post_diagonal_completion_geometry hs choice br sr wr gr bc sc wc gc
    hbr hsr hwr hgr hbc hsc hwc hgc hrows hcols
  dsimp only at hg
  have hl := fw_first_band_post_diagonal_load hn hnhi hP
  have h := balanced_residual_central_completion (r₀ := 12 * (5 + 16 + 3 * (n / 450) + P))
    (b := 0) a _ hg.1 hg.2.1 (by simpa using hl)
    (fun i => (hg.2.2.1 i).1) (by simpa using fun i => (hg.2.2.1 i).2)
    (fun i => (hg.2.2.2 i).1) (by simpa using fun i => (hg.2.2.2 i).2)
    ε hε (by simpa using hstock)
  norm_num at h ⊢
  exact h

end
end Sude
