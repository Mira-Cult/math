import Sude.BridgeWindowOverlap

/-! Connect actual selected bridge batches to labelled complete grids. -/
namespace Sude
noncomputable section

/-- The grid-preservation induction works with any fresh injective family of
physical stage labels, not only the natural numbers themselves. -/
theorem bridgeIteration_grids_on_labels {α : Type*} [DecidableEq α]
    (X R₀ : ℝ) (initial : Finset α) (label : ℕ → α) (gap : α → ℕ) (radius J : ℕ)
    (hinj : Function.Injective label)
    (hgrid : CompleteEvenGrid initial gap radius) (hradius : 2 ∣ radius)
    (hcoverage : R₀ ≤ (radius : ℝ))
    (hbelow : ∀ j < J, bridgeIteration X R₀ j < X)
    (hfresh : ∀ j < J, label j ∉ initial)
    (hgaps : ∀ j < J, 2 ∣ gap (label j) ∧
      bridgeGapLower X (bridgeIteration X R₀ j) < (gap (label j) : ℝ) ∧
      (gap (label j) : ℝ) ≤ bridgeIteration X R₀ j) :
    ∀ j ≤ J,
      CompleteEvenGrid (initial ∪ (Finset.range j).image label) gap
          (radius + ∑ i ∈ Finset.range j, gap (label i)) ∧
        2 ∣ radius + ∑ i ∈ Finset.range j, gap (label i) ∧
        bridgeIteration X R₀ j ≤
          ((radius + ∑ i ∈ Finset.range j, gap (label i) : ℕ) : ℝ) := by
  intro j hj
  induction j with
  | zero => simpa [bridgeIteration] using And.intro hgrid (And.intro hradius hcoverage)
  | succ j ih =>
    have hjJ : j < J := by omega
    have ⟨hprevGrid, hprevEven, hprevCoverage⟩ := ih (by omega)
    have ⟨hgapEven, hgapLower, hgapUpper⟩ := hgaps j hjJ
    have hnew : label j ∉ initial ∪ (Finset.range j).image label := by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, not_or]
      refine ⟨hfresh j hjJ, ?_⟩
      rintro ⟨i, hi, heq⟩
      have : i = j := hinj heq
      omega
    have hstep := bridge_extends_grid_from_lower_bound
      (initial ∪ (Finset.range j).image label) gap
      (radius + ∑ i ∈ Finset.range j, gap (label i)) (label j)
      X (bridgeIteration X R₀ j) hnew hprevEven hgapEven hprevCoverage hgapLower
      hgapUpper hprevGrid
    have hset : initial ∪ (Finset.range (j + 1)).image label =
        insert (label j) (initial ∪ (Finset.range j).image label) := by
      rw [Finset.range_add_one, Finset.image_insert, Finset.union_insert]
    have hsum : (radius + ∑ i ∈ Finset.range (j + 1), gap (label i)) =
        (radius + ∑ i ∈ Finset.range j, gap (label i)) + gap (label j) := by
      rw [Finset.sum_range_succ]
      omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hset, hsum]
      exact hstep.1
    · rw [hsum]
      exact dvd_add hprevEven hgapEven
    · rw [hsum]
      change bridgeNext X (bridgeIteration X R₀ j) ≤ _
      rw [bridgeNext, if_pos (hbelow j hjJ)]
      exact le_of_lt hstep.2

/-- The indexed gap is read from the actual block selected at that stage. -/
def selectedBridgeGap (batches : ℕ → List DoublePair) (index j : ℕ) : ℕ :=
  match (batches j)[index]? with
  | none => 0
  | some b => b.high₁ - b.low₁

theorem selectedBridgeGap_bounds (n : ℕ) (initial : Finset ℕ) (R₀ : ℝ)
    (batches : ℕ → List DoublePair) (k J : ℕ)
    (hvalid : ∀ j < J,
      bridgeStageValid n initial (bridgeIteration (poolMaximum n) R₀) batches k j)
    (index : Fin k) (j : ℕ) (hj : j < J) :
    2 ∣ selectedBridgeGap batches index j ∧
      bridgeGapLower (poolMaximum n) (bridgeIteration (poolMaximum n) R₀ j) <
        (selectedBridgeGap batches index j : ℝ) ∧
      (selectedBridgeGap batches index j : ℝ) ≤ bridgeIteration (poolMaximum n) R₀ j := by
  have hv := hvalid j hj
  have hi : index.val < (batches j).length := by rw [hv.1]; exact index.isLt
  have hb := hv.2.2.2 (batches j)[index.val] (List.getElem_mem hi)
  simp only [selectedBridgeGap, List.getElem?_eq_getElem hi]
  exact ⟨hb.1, hb.2.1, hb.2.2.2⟩

def joinedBridgeGap {α : Type*} (initialGap : α → ℕ)
    (batches : ℕ → List DoublePair) (index : ℕ) : Sum α ℕ → ℕ
  | .inl a => initialGap a
  | .inr j => selectedBridgeGap batches index j

/-- Re-label the initial physical reservoir into the left side of a
disjoint sum, leaving its complete grid and every existing gap unchanged. -/
theorem completeEvenGrid_joined {α : Type*} [DecidableEq α]
    (initial : Finset α) (initialGap : α → ℕ) (radius : ℕ)
    (batches : ℕ → List DoublePair) (index : ℕ)
    (hgrid : CompleteEvenGrid initial initialGap radius) :
    CompleteEvenGrid (initial.map ⟨Sum.inl, Sum.inl_injective⟩)
      (joinedBridgeGap initialGap batches index) radius := by
  intro t ht heven
  obtain ⟨T, hT, hsum⟩ := hgrid t ht heven
  refine ⟨T.map ⟨Sum.inl, Sum.inl_injective⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr ⟨a, hT ha, rfl⟩
  · simpa [joinedBridgeGap] using hsum

/-- Every selected block position extends an initial grid through X. The
gaps are read from the actual selected prime entries, and initial and new
labels are disjoint by construction. -/
theorem selectedBridgeBatches_grow_grid {α : Type*} [DecidableEq α]
    (n : ℕ) (reserved : Finset ℕ) (R₀ : ℝ) (batches : ℕ → List DoublePair)
    (k J : ℕ) (index : Fin k) (initial : Finset α) (initialGap : α → ℕ) (radius : ℕ)
    (hgrid : CompleteEvenGrid initial initialGap radius) (hradius : 2 ∣ radius)
    (hcoverage : R₀ ≤ (radius : ℝ))
    (hbelow : ∀ j < J, bridgeIteration (poolMaximum n) R₀ j < poolMaximum n)
    (hstop : (poolMaximum n : ℝ) ≤ bridgeIteration (poolMaximum n) R₀ J)
    (hvalid : ∀ j < J,
      bridgeStageValid n reserved (bridgeIteration (poolMaximum n) R₀) batches k j) :
    CompleteEvenGrid
        (initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
          (Finset.range J).image (Sum.inr : ℕ → Sum α ℕ))
        (joinedBridgeGap initialGap batches index)
        (radius + ∑ j ∈ Finset.range J, selectedBridgeGap batches index j) ∧
      (poolMaximum n : ℝ) ≤
        ((radius + ∑ j ∈ Finset.range J, selectedBridgeGap batches index j : ℕ) : ℝ) := by
  let init' : Finset (Sum α ℕ) := initial.map ⟨Sum.inl, Sum.inl_injective⟩
  let label : ℕ → Sum α ℕ := Sum.inr
  let joined := joinedBridgeGap initialGap batches index
  have hgrid' : CompleteEvenGrid init' joined radius :=
    completeEvenGrid_joined initial initialGap radius batches index hgrid
  have hfresh : ∀ j < J, label j ∉ init' := by
    intro j _ hj
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hj
    cases ha
  have hgaps : ∀ j < J, 2 ∣ joined (label j) ∧
      bridgeGapLower (poolMaximum n) (bridgeIteration (poolMaximum n) R₀ j) <
        (joined (label j) : ℝ) ∧
      (joined (label j) : ℝ) ≤ bridgeIteration (poolMaximum n) R₀ j := by
    intro j hj
    exact selectedBridgeGap_bounds n reserved R₀ batches k J hvalid index j hj
  have hseq := bridgeIteration_grids_on_labels (poolMaximum n) R₀ init' label joined radius J
    Sum.inr_injective hgrid' hradius hcoverage hbelow hfresh hgaps J le_rfl
  exact ⟨hseq.1, le_trans hstop hseq.2.2⟩

/-- Under the published analytic inputs and explicit numerical bridge
budgets, select all stages and extend each indexed initial grid through X
using the gaps of the actual, mutually disjoint selected blocks. -/
theorem select_bridge_and_grow_grids {α : Type*} [DecidableEq α]
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (n : ℕ) (reserved : Finset ℕ)
    (R₀ : ℝ) (M : ℕ → ℕ) (k : ℕ)
    (initial : Fin k → Finset α) (initialGap : Fin k → α → ℕ) (radius : Fin k → ℕ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hR : 0 < R₀)
    (hgrid : ∀ i, CompleteEvenGrid (initial i) (initialGap i) (radius i))
    (hradius : ∀ i, 2 ∣ radius i) (hcoverage : ∀ i, R₀ ≤ (radius i : ℝ))
    (hbudget : ∀ j, bridgeIteration (poolMaximum n) R₀ j < poolMaximum n →
      bridgeGeometricStageBudget n reserved (bridgeIteration (poolMaximum n) R₀) (M j) k j) :
    ∃ J : ℕ, ∃ batches : ℕ → List DoublePair,
      (∀ j < J, bridgeStageValid n reserved (bridgeIteration (poolMaximum n) R₀) batches k j) ∧
      (∀ i < J, ∀ j < J, i ≠ j →
        Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
          (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))) ∧
      (∀ i : Fin k,
        CompleteEvenGrid
          ((initial i).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
            (Finset.range J).image (Sum.inr : ℕ → Sum α ℕ))
          (joinedBridgeGap (initialGap i) batches i)
          (radius i + ∑ j ∈ Finset.range J, selectedBridgeGap batches i j) ∧
        (poolMaximum n : ℝ) ≤
          ((radius i + ∑ j ∈ Finset.range J, selectedBridgeGap batches i j : ℕ) : ℝ)) := by
  obtain ⟨J, batches, hstop, hbelow, hvalid, hdisjoint⟩ :=
    select_bridge_until_covered bmor upper n reserved R₀ M k hn hnmax hR hbudget
  refine ⟨J, batches, hvalid, hdisjoint, ?_⟩
  intro i
  exact selectedBridgeBatches_grow_grid n reserved R₀ batches k J i (initial i) (initialGap i)
    (radius i) (hgrid i) (hradius i) (hcoverage i) hbelow hstop hvalid

end
end Sude
