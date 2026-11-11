import Sude.FWBridgeFiveBatch

/-! Selected nominal FW batches against their actual cumulative reservation. -/
namespace Sude
noncomputable section

/-- Each of the five supplied nominal batches is valid after the actual
initial-and-earlier reservation. The equality of each current stock's
reservation intersection records why no new same-side charge is needed. -/
def FWBridgeSequentialValid (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair) (j : ℕ) : Prop :=
  let X : ℝ := poolMaximum n
  let R := fwBridgeRadius X j
  let prior := priorBridgeReservation initial (Finset.range j) batches
  FWBridgeBatchValid n initial batches j ∧
    (∀ b ∈ batches j, b.valid (fwBridgeLowStock X R \ prior) (fwBridgeHighStock X R \ prior)) ∧
    (∀ b ∈ batches j, Disjoint b.footprint prior) ∧
    prior ∩ fwBridgeLowStock X R = initial ∩ fwBridgeLowStock X R ∧
    prior ∩ fwBridgeHighStock X R = initial ∩ fwBridgeHighStock X R

/-- Any five valid nominal batches also meet the stronger actual sequential
reservation interface. No numerical stock estimate is introduced. -/
theorem fw_five_batches_sequential_valid (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeBatchValid n initial batches j) :
    ∀ j < 5, FWBridgeSequentialValid n initial batches j := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  intro j hj
  let X : ℝ := poolMaximum n
  let R := fwBridgeRadius X j
  let prior := priorBridgeReservation initial (Finset.range j) batches
  have hprevious : ∀ i < j, ∀ b ∈ batches i,
      b.valid (fwBridgeLowStock X (fwBridgeRadius X i))
        (fwBridgeHighStock X (fwBridgeRadius X i)) := by
    intro i hi b hb
    have hi5 : i < 5 := by omega
    exact DoublePair.valid_mono ((hvalid i hi5).2.1 b hb) Finset.sdiff_subset Finset.sdiff_subset
  have hinter := fw_nominal_prior_reservation_intersections X hX initial batches j hj hprevious
  have hlow : fwBridgeLowStock X R \ initial ⊆ fwBridgeLowStock X R \ prior := by
    intro p hp
    obtain ⟨hstock, hnot⟩ := Finset.mem_sdiff.mp hp
    refine Finset.mem_sdiff.mpr ⟨hstock, ?_⟩
    intro hprior
    have hm : p ∈ initial ∩ fwBridgeLowStock X R := by
      rw [← hinter.1]
      exact Finset.mem_inter.mpr ⟨hprior, hstock⟩
    exact hnot (Finset.mem_inter.mp hm).1
  have hhigh : fwBridgeHighStock X R \ initial ⊆ fwBridgeHighStock X R \ prior := by
    intro p hp
    obtain ⟨hstock, hnot⟩ := Finset.mem_sdiff.mp hp
    refine Finset.mem_sdiff.mpr ⟨hstock, ?_⟩
    intro hprior
    have hm : p ∈ initial ∩ fwBridgeHighStock X R := by
      rw [← hinter.2]
      exact Finset.mem_inter.mpr ⟨hprior, hstock⟩
    exact hnot (Finset.mem_inter.mp hm).1
  have hafter : ∀ b ∈ batches j,
      b.valid (fwBridgeLowStock X R \ prior) (fwBridgeHighStock X R \ prior) := by
    intro b hb
    exact DoublePair.valid_mono ((hvalid j hj).2.1 b hb) hlow hhigh
  refine ⟨hvalid j hj, hafter, ?_, hinter.1, hinter.2⟩
  intro b hb
  have hv := hafter b hb
  apply Finset.disjoint_left.mpr
  intro p hp hr
  simp only [DoublePair.footprint, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact (Finset.mem_sdiff.mp hv.1).2 hr
  · exact (Finset.mem_sdiff.mp hv.2.1).2 hr
  · exact (Finset.mem_sdiff.mp hv.2.2.1).2 hr
  · exact (Finset.mem_sdiff.mp hv.2.2.2.1).2 hr

/-- The full reservation of any initial segment is bounded by the actual
initial cardinality plus four endpoints per supplied block. -/
theorem fw_five_batches_prior_card_le (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeBatchValid n initial batches j)
    (j : ℕ) (hj : j ≤ 5) :
    (priorBridgeReservation initial (Finset.range j) batches).card ≤
      initial.card + j * (4 * (3 * (n + 8))) := by
  have hstage : ∀ i ∈ Finset.range j,
      (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i)).card ≤ 4 * (3 * (n + 8)) := by
    intro i hi
    have hi5 : i < 5 := by have := Finset.mem_range.mp hi; omega
    have hlen := (hvalid i hi5).1
    have hl := doubleBatchLow_card_le (batches i)
    have hh := doubleBatchHigh_card_le (batches i)
    have hu := Finset.card_union_le (doubleBatchLow (batches i)) (doubleBatchHigh (batches i))
    rw [hlen] at hl hh
    omega
  have hbatch := Finset.card_biUnion_le_card_mul (Finset.range j)
    (fun i => doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
    (4 * (3 * (n + 8))) hstage
  have hunion := Finset.card_union_le initial ((Finset.range j).biUnion
    (fun i => doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i)))
  simp only [Finset.card_range] at hbatch
  change (initial ∪ (Finset.range j).biUnion
    (fun i => doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))).card ≤ _
  exact hunion.trans (Nat.add_le_add_left hbatch initial.card)

/-- Under the original published hypotheses and each explicit stock and
square gate, the selected five nominal batches satisfy the actual sequential
reservation interface and the cumulative cardinal bound. No physical line
geometry, complete grid, or numerical gate is established. -/
theorem bmor_fw_five_bridge_batches_sequential
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
      (∀ j < 5, FWBridgeSequentialValid n initial batches j) ∧
      (∀ i < 5, ∀ j < 5, i ≠ j →
        Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
          (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))) ∧
      (∀ j ≤ 5, (priorBridgeReservation initial (Finset.range j) batches).card ≤
        initial.card + j * (4 * (3 * (n + 8)))) := by
  obtain ⟨batches, hvalid, hdisjoint⟩ :=
    bmor_fw_five_bridge_batches bmor upper n initial M hn hnmax hbudgetLow hbudgetHigh hgate
  exact ⟨batches, fw_five_batches_sequential_valid n initial batches hvalid, hdisjoint,
    fw_five_batches_prior_card_le n initial batches hvalid⟩

end
end Sude
