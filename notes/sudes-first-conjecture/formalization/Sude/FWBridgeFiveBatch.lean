import Sude.FWBridgeDepletion

/-! Conditional selection of the five nominal FW bridge batches. -/
namespace Sude
noncomputable section

/-- A stage records the actual selected batch, its common reservation,
and the source gap bounds.  The numerical gates are not part of this
predicate and must be supplied to the selection theorem. -/
def FWBridgeBatchValid (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair) (j : ℕ) : Prop :=
  let X : ℝ := poolMaximum n
  let R := fwBridgeRadius X j
  (batches j).length = 3 * (n + 8) ∧
    (∀ b ∈ batches j, b.valid (fwBridgeLowStock X R \ initial)
      (fwBridgeHighStock X R \ initial)) ∧
    (batches j).Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
    (∀ b ∈ batches j, Disjoint b.footprint initial) ∧
    (∀ b ∈ batches j, 0 < b.high₁ - b.low₁ ∧ 2 ∣ b.high₁ - b.low₁ ∧
      (208 / 231 : ℝ) * bridgeSpan X R < ((b.high₁ - b.low₁ : ℕ) : ℝ) ∧
      ((b.high₁ - b.low₁ : ℕ) : ℝ) < bridgeSpan X R ∧
      ((b.high₁ - b.low₁ : ℕ) : ℝ) ≤ R)

/-- Five nominal FW stages can be selected from the actual pool after the
same arbitrary initial reservation. Each stage's stock and square gates
are explicit hypotheses. This provides no
physical placement, numerical certificate, or complete-grid conclusion. -/
theorem bmor_fw_five_bridge_batches
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (n : ℕ)
    (initial : Finset ℕ) (M : ℕ → ℕ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hbudgetLow : ∀ j < 5,
      ((M j + 2 * (3 * (n + 8)) +
        (fwBridgeLowStock (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) ∩ initial).card : ℕ) : ℝ) ≤
          fwBridgeStockBound (poolMaximum n) (fwBridgeRadius (poolMaximum n) j))
    (hbudgetHigh : ∀ j < 5,
      ((M j + 2 * (3 * (n + 8)) +
        (fwBridgeHighStock (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) ∩ initial).card : ℕ) : ℝ) ≤
          fwBridgeStockBound (poolMaximum n) (fwBridgeRadius (poolMaximum n) j))
    (hgate : ∀ j < 5,
      fwBridgeWidth (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) + 1 <
        (M j : ℝ) * M j) :
    ∃ batches : ℕ → List DoublePair,
      (∀ j < 5, FWBridgeBatchValid n initial batches j) ∧
      (∀ i < 5, ∀ j < 5, i ≠ j →
        Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
          (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))) := by
  classical
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hex : ∀ j, j < 5 → ∃ blocks : List DoublePair,
      blocks.length = 3 * (n + 8) ∧
      (∀ b ∈ blocks, b.valid
        (fwBridgeLowStock (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) \ initial)
        (fwBridgeHighStock (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) \ initial)) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
      (∀ b ∈ blocks, Disjoint b.footprint initial) ∧
      (∀ b ∈ blocks, 0 < b.high₁ - b.low₁ ∧ 2 ∣ b.high₁ - b.low₁ ∧
        (208 / 231 : ℝ) * bridgeSpan (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) <
          ((b.high₁ - b.low₁ : ℕ) : ℝ) ∧
        ((b.high₁ - b.low₁ : ℕ) : ℝ) < bridgeSpan (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) ∧
        ((b.high₁ - b.low₁ : ℕ) : ℝ) ≤ fwBridgeRadius (poolMaximum n) j) := by
    intro j hj
    exact bmor_fw_bridge_select_pool_blocks bmor upper n
      (fwBridgeRadius (poolMaximum n) j) initial (M j) (3 * (n + 8)) hn hnmax
      (fw_bridge_nominal_radius_pos (poolMaximum n) hX j hj)
      (hbudgetLow j hj) (hbudgetHigh j hj) (hgate j hj)
  let batches : ℕ → List DoublePair := fun j =>
    if hj : j < 5 then Classical.choose (hex j hj) else []
  have hvalid : ∀ j < 5, FWBridgeBatchValid n initial batches j := by
    intro j hj
    have h := Classical.choose_spec (hex j hj)
    simpa only [FWBridgeBatchValid, batches, dif_pos hj] using h
  refine ⟨batches, hvalid, ?_⟩
  intro i hi j hj hij
  have hiValid := (hvalid i hi).2.1
  have hjValid := (hvalid j hj).2.1
  have hiLow : doubleBatchLow (batches i) ⊆
      fwBridgeLowStock (poolMaximum n) (fwBridgeRadius (poolMaximum n) i) := by
    apply doubleBatchLow_subset _ _ _
    intro b hb
    exact DoublePair.valid_mono (hiValid b hb) Finset.sdiff_subset Finset.sdiff_subset
  have hiHigh : doubleBatchHigh (batches i) ⊆
      fwBridgeHighStock (poolMaximum n) (fwBridgeRadius (poolMaximum n) i) := by
    apply doubleBatchHigh_subset _ _ _
    intro b hb
    exact DoublePair.valid_mono (hiValid b hb) Finset.sdiff_subset Finset.sdiff_subset
  have hjLow : doubleBatchLow (batches j) ⊆
      fwBridgeLowStock (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) := by
    apply doubleBatchLow_subset _ _ _
    intro b hb
    exact DoublePair.valid_mono (hjValid b hb) Finset.sdiff_subset Finset.sdiff_subset
  have hjHigh : doubleBatchHigh (batches j) ⊆
      fwBridgeHighStock (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) := by
    apply doubleBatchHigh_subset _ _ _
    intro b hb
    exact DoublePair.valid_mono (hjValid b hb) Finset.sdiff_subset Finset.sdiff_subset
  have hll := fw_bridge_nominal_low_stocks_disjoint (poolMaximum n) hX i j hi hj hij
  have hhh := fw_bridge_nominal_high_stocks_disjoint (poolMaximum n) hX i j hi hj hij
  have hri := fw_bridge_nominal_radius_pos (poolMaximum n) hX i hi
  have hrj := fw_bridge_nominal_radius_pos (poolMaximum n) hX j hj
  have hlh := fw_bridge_low_high_stocks_disjoint (poolMaximum n) _ _ hX hri hrj
  have hhl := (fw_bridge_low_high_stocks_disjoint (poolMaximum n) _ _ hX hrj hri).symm
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact Finset.disjoint_left.mp hll (hiLow hx) (hjLow hy)
  · exact Finset.disjoint_left.mp hlh (hiLow hx) (hjHigh hy)
  · exact Finset.disjoint_left.mp hhl (hiHigh hx) (hjLow hy)
  · exact Finset.disjoint_left.mp hhh (hiHigh hx) (hjHigh hy)

end
end Sude
