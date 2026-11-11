import Sude.FWGroupedPairMassReindex
import Sude.FWFourFamilyStageTotals
import Sude.DoubleBlockStageMeanPreservation

/-! Exact reindexing of FW stage midpoint averages between pair slots and
double-block slots. No source mean bound or concentration is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384

/-- Regrouping the 6(n+8) oriented pairs as 3(n+8) two-pair blocks preserves
their average midpoint, with the block normalization handled explicitly. -/
theorem fw_grouped_stage_midpoint_mean {P n : ℕ}
    (cells : ((Fin P × Fin (6 * (n + 8))) × Bool) → Cell n)
    (a : Cell n ≃ Fin (n*n)) (j : Fin P) :
    (∑ q, (((entry a (cells ((j,q),false)) : ℝ) + entry a (cells ((j,q),true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ) =
      doubleStageMidpointMean (cells ∘ fwBlockPairIndex P n) a j := by
  classical
  let f := fun q : Fin (6 * (n + 8)) =>
    (((entry a (cells ((j,q),false)) : ℝ) + entry a (cells ((j,q),true))) / 2)
  have hsum : (∑ q, f q) = ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      doubleBlockPairMidpoint (cells ∘ fwBlockPairIndex P n) a j b p := by
    calc
      _ = ∑ x : Fin (3 * (n + 8)) × Fin 2, f (fwGroupedStagePairEquiv n x) :=
        (Equiv.sum_comp (fwGroupedStagePairEquiv n) f).symm
      _ = _ := by rw [Fintype.sum_prod_type]; rfl
  have hpos : (0 : ℝ) < (3 * (n + 8) : ℕ) := by exact_mod_cast (by omega : 0 < 3 * (n + 8))
  have hcast : ((6 * (n + 8) : ℕ) : ℝ) = 2 * ((3 * (n + 8) : ℕ) : ℝ) := by push_cast; ring
  change (∑ q, f q) / ((6 * (n + 8) : ℕ) : ℝ) = _
  rw [hsum, hcast]
  unfold doubleStageMidpointMean doubleBlockMidpoint
  simp only [Fin.sum_univ_two]
  rw [← Finset.sum_div]
  field_simp

/-- The original FWFourFamily bridge and wide stage means are exactly the
means of the corresponding grouped physical maps on the same square. -/
theorem fw_four_family_bridge_wide_grouped_means {n P L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (a : Cell n ≃ Fin (n*n)) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hr hc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let mean := fun j : FWFourStageIndex n P =>
      (∑ i, (((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
    (∀ j : Fin 5, mean (Sum.inl (Sum.inl (Sum.inl j))) =
      doubleStageMidpointMean (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc) a j) ∧
    (∀ j : Fin (3 * (n / 450)), mean (Sum.inl (Sum.inr j)) =
      doubleStageMidpointMean (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) a j) := by
  constructor
  · intro j
    exact fw_grouped_stage_midpoint_mean (fwBridgePhysicalPairCells hrect hs choice br bc hr hc) a j
  · intro j
    exact fw_grouped_stage_midpoint_mean (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc) a j

/-- Under the supplied same-side block reallocation equations, every actual
FW bridge and wide stage mean on `new` equals that on its source `old`. -/
theorem fw_four_family_bridge_wide_means_preserved {n P L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (old new : Cell n ≃ Fin (n*n))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8)))) (sb : Fin 5 → Fin (3 * (n + 8)) → Bool)
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (sw : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → Bool)
    (hbridge : ∀ j b p side, entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),side)) =
      entry old (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,πb j b,doubleBlockPairSwap (sb j b) p),side)))
    (hwideEntry : ∀ j b p side, entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),side)) =
      entry old (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,πw j b,doubleBlockPairSwap (sw j b) p),side))) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hr hc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let mean := fun a j =>
      (∑ i, (((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
    (∀ j : Fin 5, mean new (Sum.inl (Sum.inl (Sum.inl j))) = mean old (Sum.inl (Sum.inl (Sum.inl j)))) ∧
    (∀ j : Fin (3 * (n / 450)), mean new (Sum.inl (Sum.inr j)) = mean old (Sum.inl (Sum.inr j))) := by
  have hnew := fw_four_family_bridge_wide_grouped_means hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hr hc hsr hsc hwr hwc hgr hgc new
  have hold := fw_four_family_bridge_wide_grouped_means hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hr hc hsr hsc hwr hwc hgr hgc old
  have hpres := double_block_bridge_wide_stage_means_preserved
    (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc)
    (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) old new πb sb πw sw hbridge hwideEntry
  exact ⟨fun j => (hnew.1 j).trans ((hpres.1 j).trans (hold.1 j).symm),
    fun j => (hnew.2 j).trans ((hpres.2 j).trans (hold.2 j).symm)⟩

end
end Sude
