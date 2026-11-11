import Sude.FWBridgeGridGrowth

/-! Rebuild the abstract FW bridge grid using a possibly different actual
source block at each stage. No physical placement or concentration is asserted. -/
namespace Sude
noncomputable section

/-- Each bridge-stage label reads the gap from that stage's chosen block. -/
def fwStageVaryingJoinedBridgeGap {α : Type*} {n : ℕ} (initialGap : α → ℕ)
    (batches : ℕ → List DoublePair) (index : ℕ → Fin (3 * (n + 8))) : Sum α ℕ → ℕ
  | .inl a => initialGap a
  | .inr j => selectedBridgeGap batches (index j) j

/-- A fresh source index at each stage produces a complete grid through X.
The final radius is the sum of the actual selected gaps, and need not equal
the radius before a stage-wise permutation. -/
theorem fw_stage_varying_bridge_batches_grow_grid {α : Type*} [DecidableEq α]
    (n : ℕ) (reserved : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n reserved batches j)
    (index : ℕ → Fin (3 * (n + 8)))
    (initial : Finset α) (initialGap : α → ℕ) (radius : ℕ)
    (hgrid : CompleteEvenGrid initial initialGap radius) (hradius : 2 ∣ radius)
    (hcoverage : (poolMaximum n : ℝ) / 23 ≤ radius) :
    CompleteEvenGrid
      (initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        (Finset.range 5).image (Sum.inr : ℕ → Sum α ℕ))
      (fwStageVaryingJoinedBridgeGap initialGap batches index)
      (radius + ∑ j ∈ Finset.range 5, selectedBridgeGap batches (index j) j) ∧
    (poolMaximum n : ℝ) ≤
      ((radius + ∑ j ∈ Finset.range 5, selectedBridgeGap batches (index j) j : ℕ) : ℝ) := by
  classical
  let X : ℝ := poolMaximum n
  let init' : Finset (Sum α ℕ) := initial.map ⟨Sum.inl, Sum.inl_injective⟩
  let label : ℕ → Sum α ℕ := Sum.inr
  let gap := fwStageVaryingJoinedBridgeGap initialGap batches index
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hbase : CompleteEvenGrid init' gap radius := by
    intro t ht heven
    obtain ⟨T, hT, hsum⟩ := hgrid t ht heven
    refine ⟨T.map ⟨Sum.inl, Sum.inl_injective⟩, ?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_map.mpr ⟨a, hT ha, rfl⟩
    · simpa [gap, fwStageVaryingJoinedBridgeGap] using hsum
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
      have hg := fw_selected_bridge_gap_bounds n reserved batches hvalid (index j) j hj5
      have hjoin : gap (label j) ≤ radius + ∑ i ∈ Finset.range j, gap (label i) := by
        have hreal : (gap (label j) : ℝ) ≤
            ((radius + ∑ i ∈ Finset.range j, gap (label i) : ℕ) : ℝ) := by
          exact (show (selectedBridgeGap batches (index j) j : ℝ) ≤ fwBridgeRadius X j from hg.2.2).trans hcov
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



/-- A destination block reads its stage's permuted source; outside the five
stages the value is a harmless default and is never used by the grid. -/
def fwPermutedBridgeIndex {n : ℕ}
    (ω : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (destination : Fin (3 * (n + 8))) (j : ℕ) : Fin (3 * (n + 8)) :=
  if h : j < 5 then ω ⟨j, h⟩ destination else destination

/-- Rebuild the abstract grid using the actual source of a destination block
at each permuted stage. The retained gaps and radius are the recomputed ones;
physical slot transport remains a separate obligation. -/
theorem fw_permuted_bridge_batches_grow_grid {α : Type*} [DecidableEq α]
    (n : ℕ) (reserved : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n reserved batches j)
    (ω : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (destination : Fin (3 * (n + 8)))
    (initial : Finset α) (initialGap : α → ℕ) (radius : ℕ)
    (hgrid : CompleteEvenGrid initial initialGap radius) (hradius : 2 ∣ radius)
    (hcoverage : (poolMaximum n : ℝ) / 23 ≤ radius) :
    CompleteEvenGrid
      (initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        (Finset.range 5).image (Sum.inr : ℕ → Sum α ℕ))
      (fwStageVaryingJoinedBridgeGap initialGap batches (fwPermutedBridgeIndex ω destination))
      (radius + ∑ j ∈ Finset.range 5,
        selectedBridgeGap batches (fwPermutedBridgeIndex ω destination j) j) ∧
    (poolMaximum n : ℝ) ≤
      ((radius + ∑ j ∈ Finset.range 5,
        selectedBridgeGap batches (fwPermutedBridgeIndex ω destination j) j : ℕ) : ℝ) := by
  exact fw_stage_varying_bridge_batches_grow_grid n reserved batches hvalid
    (fwPermutedBridgeIndex ω destination) initial initialGap radius hgrid hradius hcoverage

end
end Sude
