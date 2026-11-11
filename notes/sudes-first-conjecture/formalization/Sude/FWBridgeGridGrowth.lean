import Sude.FWBridgeFiveSequential
import Sude.BridgeChosenGrid

/-! Conditional complete-grid growth from actual nominal FW bridge batches. -/
namespace Sude
noncomputable section

/-- A fixed block index reads one actual even gap from every nominal FW
batch. The stages are not asserted to exist without their selection gates. -/
theorem fw_selected_bridge_gap_bounds (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (index : Fin (3 * (n + 8))) (j : ℕ) (hj : j < 5) :
    2 ∣ selectedBridgeGap batches index j ∧
      fwBridgeGapLower (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) <
        (selectedBridgeGap batches index j : ℝ) ∧
      (selectedBridgeGap batches index j : ℝ) ≤ fwBridgeRadius (poolMaximum n) j := by
  have hv : FWBridgeBatchValid n initial batches j := (hvalid j hj).1
  have hi : index.val < (batches j).length := by rw [hv.1]; exact index.isLt
  have hb := hv.2.2.2.2 (batches j)[index.val] (List.getElem_mem hi)
  simp only [selectedBridgeGap, List.getElem?_eq_getElem hi]
  refine ⟨hb.2.1, ?_, hb.2.2.2.2⟩
  rw [(fw_bridge_width_and_increment (poolMaximum n) (fwBridgeRadius (poolMaximum n) j)).2]
  exact hb.2.2.1

/-- If an existing labelled even grid covers `X/23`, then a fixed block
position in all five FW batches extends it through `X`.  The gap labels
are formal disjoint-sum labels; physical slot assignment and diagonal
or network geometry are separate obligations. -/
theorem fw_selected_bridge_batches_grow_grid {α : Type*} [DecidableEq α]
    (n : ℕ) (reserved : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n reserved batches j)
    (index : Fin (3 * (n + 8)))
    (initial : Finset α) (initialGap : α → ℕ) (radius : ℕ)
    (hgrid : CompleteEvenGrid initial initialGap radius) (hradius : 2 ∣ radius)
    (hcoverage : (poolMaximum n : ℝ) / 23 ≤ radius) :
    CompleteEvenGrid
      (initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        (Finset.range 5).image (Sum.inr : ℕ → Sum α ℕ))
      (joinedBridgeGap initialGap batches index)
      (radius + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j) ∧
    (poolMaximum n : ℝ) ≤
      ((radius + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j : ℕ) : ℝ) := by
  classical
  let X : ℝ := poolMaximum n
  let init' : Finset (Sum α ℕ) := initial.map ⟨Sum.inl, Sum.inl_injective⟩
  let label : ℕ → Sum α ℕ := Sum.inr
  let gap := joinedBridgeGap initialGap batches index
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hbase : CompleteEvenGrid init' gap radius :=
    completeEvenGrid_joined initial initialGap radius batches index hgrid
  have hseq : ∀ j ≤ 5,
      CompleteEvenGrid (init' ∪ (Finset.range j).image label) gap
        (radius + ∑ i ∈ Finset.range j, gap (label i)) ∧
      2 ∣ radius + ∑ i ∈ Finset.range j, gap (label i) ∧
      fwBridgeRadius X j ≤
        ((radius + ∑ i ∈ Finset.range j, gap (label i) : ℕ) : ℝ) := by
    intro j hj
    induction j with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simpa using hbase
      · simpa using hradius
      · simpa [fwBridgeRadius, fwBridgeRatio, X, div_eq_mul_inv, mul_comm] using hcoverage
    | succ j ih =>
      have hj5 : j < 5 := by omega
      have ⟨hprev, heven, hcov⟩ := ih (by omega)
      have hg := fw_selected_bridge_gap_bounds n reserved batches hvalid index j hj5
      have hjoin : gap (label j) ≤ radius + ∑ i ∈ Finset.range j, gap (label i) := by
        have hreal : (gap (label j) : ℝ) ≤
            ((radius + ∑ i ∈ Finset.range j, gap (label i) : ℕ) : ℝ) := by
          exact (show (selectedBridgeGap batches index j : ℝ) ≤ fwBridgeRadius X j from hg.2.2).trans hcov
        exact_mod_cast hreal
      have hfresh : label j ∉ init' ∪ (Finset.range j).image label := by
        simp [init', label]
      have hstep := completeEvenGrid_insert (init' ∪ (Finset.range j).image label)
        gap (radius + ∑ i ∈ Finset.range j, gap (label i)) (label j)
        hfresh heven hg.1 (by omega) hprev
      have hset : init' ∪ (Finset.range (j + 1)).image label =
          insert (label j) (init' ∪ (Finset.range j).image label) := by
        rw [Finset.range_add_one, Finset.image_insert, Finset.union_insert]
      have hsum : radius + ∑ i ∈ Finset.range (j + 1), gap (label i) =
          (radius + ∑ i ∈ Finset.range j, gap (label i)) + gap (label j) := by
        rw [Finset.sum_range_succ]
        omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hset, hsum]
        exact hstep
      · rw [hsum]
        exact dvd_add heven hg.1
      · rw [hsum, fw_bridge_radius_succ X hX j]
        have hgapreal : fwBridgeGapLower X (fwBridgeRadius X j) < (gap (label j) : ℝ) := hg.2.1
        push_cast at hcov
        push_cast
        linarith
  have hfinal := hseq 5 le_rfl
  have hstop : X ≤ fwBridgeRadius X 5 := by
    have h := fw_bridge_five_stage_schedule.2.2.2.2.2.2.2.2
    dsimp [fwBridgeRadius]
    nlinarith
  exact ⟨hfinal.1, hstop.trans hfinal.2.2⟩

end
end Sude
