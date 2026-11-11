import Sude.BridgeStageSequence

/-! Geometric overlap accounting for FC2K bridge windows. -/
namespace Sude
noncomputable section

/-- Two half-open real windows may meet only when each lower endpoint is
strictly below the other's upper endpoint. -/
def geometricallyOverlappingWindows (active : Finset ℕ) (left right : ℕ → ℝ)
    (targetLeft targetRight : ℝ) : Finset ℕ :=
  active.filter fun j => left j < targetRight ∧ targetLeft < right j

/-- Any overlap of actual prime stocks is charged by the corresponding
geometric window overlap. The geometric count may conservatively overpay. -/
theorem prime_overlap_card_le_geometric (active : Finset ℕ) (left right : ℕ → ℝ)
    (targetLeft targetRight : ℝ)
    (hendpoints : ∀ j ∈ active, 0 ≤ left j ∧ 0 ≤ right j)
    (htarget : 0 ≤ targetLeft ∧ 0 ≤ targetRight) :
    (overlappingBridgeWindows active (fun j => apInterval (left j) (right j) 2 1)
      (apInterval targetLeft targetRight 2 1)).card ≤
        (geometricallyOverlappingWindows active left right targetLeft targetRight).card := by
  apply Finset.card_le_card
  intro j hj
  have ⟨hjactive, hmeet⟩ := Finset.mem_filter.mp hj
  obtain ⟨p, hp, htargetp⟩ := Finset.not_disjoint_iff.mp hmeet
  have hw := (mem_apInterval_iff (left j) (right j) 2 1
    (hendpoints j hjactive).1 (hendpoints j hjactive).2 p).mp hp
  have ht := (mem_apInterval_iff targetLeft targetRight 2 1 htarget.1 htarget.2 p).mp htargetp
  apply Finset.mem_filter.mpr
  exact ⟨hjactive, by constructor <;> linarith [hw.2.1, hw.2.2.1, ht.2.1, ht.2.2.1]⟩

def bridgeLowGeometricOverlap (X : ℝ) (radii : ℕ → ℝ) (j : ℕ) : Finset ℕ :=
  geometricallyOverlappingWindows (Finset.range j)
    (fun i => bridgeLowStart X (radii i)) (fun i => bridgeLowEnd X (radii i))
    (bridgeLowStart X (radii j)) (bridgeLowEnd X (radii j))

def bridgeHighGeometricOverlap (X : ℝ) (radii : ℕ → ℝ) (j : ℕ) : Finset ℕ :=
  geometricallyOverlappingWindows (Finset.range j)
    (fun i => bridgeHighStart X (radii i)) (fun i => bridgeHighEnd X (radii i))
    (bridgeHighStart X (radii j)) (bridgeHighEnd X (radii j))

theorem bridgeLow_overlap_le_geometric (X : ℝ) (radii : ℕ → ℝ) (j : ℕ)
    (hX : 0 < X) (hpositive : ∀ i ≤ j, 0 < radii i) :
    (overlappingBridgeWindows (Finset.range j) (fun i => bridgeLowStock X (radii i))
      (bridgeLowStock X (radii j))).card ≤ (bridgeLowGeometricOverlap X radii j).card := by
  apply prime_overlap_card_le_geometric
  · intro i hi
    have hg := bridge_window_geometry X (radii i) hX (hpositive i (by
      have := Finset.mem_range.mp hi; omega))
    exact ⟨by linarith [hg.2.2.1], by linarith [hg.2.2.1, hg.2.2.2.1]⟩
  · have hg := bridge_window_geometry X (radii j) hX (hpositive j le_rfl)
    exact ⟨by linarith [hg.2.2.1], by linarith [hg.2.2.1, hg.2.2.2.1]⟩

theorem bridgeHigh_overlap_le_geometric (X : ℝ) (radii : ℕ → ℝ) (j : ℕ)
    (hX : 0 < X) (hpositive : ∀ i ≤ j, 0 < radii i) :
    (overlappingBridgeWindows (Finset.range j) (fun i => bridgeHighStock X (radii i))
      (bridgeHighStock X (radii j))).card ≤ (bridgeHighGeometricOverlap X radii j).card := by
  apply prime_overlap_card_le_geometric
  · intro i hi
    have hg := bridge_window_geometry X (radii i) hX (hpositive i (by
      have := Finset.mem_range.mp hi; omega))
    exact ⟨by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1],
      by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1]⟩
  · have hg := bridge_window_geometry X (radii j) hX (hpositive j le_rfl)
    exact ⟨by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1],
      by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1]⟩

/-- The source budget counts geometric overlaps, including the full
current-stage charge and the exact initially protected entries. -/
def bridgeGeometricStageBudget (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ)
    (M k j : ℕ) : Prop :=
  let X : ℝ := poolMaximum n
  let R := radii j
  ((M + 2 * k + (initial ∩ bridgeLowStock X R).card +
    2 * k * (bridgeLowGeometricOverlap X radii j).card : ℕ) : ℝ) ≤
      bridgeStockBound X R ∧
  ((M + 2 * k + (initial ∩ bridgeHighStock X R).card +
    2 * k * (bridgeHighGeometricOverlap X radii j).card : ℕ) : ℝ) ≤
      bridgeStockBound X R ∧
  bridgeWidth X R + 1 < (M : ℝ) * M

theorem bridgeStageBudget_of_geometric (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ)
    (M k j : ℕ) (hpositive : ∀ i ≤ j, 0 < radii i)
    (hbudget : bridgeGeometricStageBudget n initial radii M k j) :
    bridgeStageBudget n initial radii M k j := by
  let X : ℝ := poolMaximum n
  have hX : 0 < X := by
    change (0 : ℝ) < (poolMaximum n : ℝ)
    exact_mod_cast (poolMaximum_prime n).pos
  have hl := bridgeLow_overlap_le_geometric X radii j hX hpositive
  have hh := bridgeHigh_overlap_le_geometric X radii j hX hpositive
  have hloMul := Nat.mul_le_mul_left (2 * k) hl
  have hhiMul := Nat.mul_le_mul_left (2 * k) hh
  have ⟨hbudgetLow, hbudgetHigh, hgate⟩ := hbudget
  refine ⟨?_, ?_, hgate⟩
  · have hnat : M + 2 * k + (initial ∩ bridgeLowStock X (radii j)).card +
        2 * k * (overlappingBridgeWindows (Finset.range j)
          (fun i => bridgeLowStock X (radii i)) (bridgeLowStock X (radii j))).card ≤
      M + 2 * k + (initial ∩ bridgeLowStock X (radii j)).card +
        2 * k * (bridgeLowGeometricOverlap X radii j).card :=
      Nat.add_le_add_left hloMul _
    have hreal : ((M + 2 * k + (initial ∩ bridgeLowStock X (radii j)).card +
        2 * k * (overlappingBridgeWindows (Finset.range j)
          (fun i => bridgeLowStock X (radii i)) (bridgeLowStock X (radii j))).card : ℕ) : ℝ) ≤
      ((M + 2 * k + (initial ∩ bridgeLowStock X (radii j)).card +
        2 * k * (bridgeLowGeometricOverlap X radii j).card : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact hreal.trans hbudgetLow
  · have hnat : M + 2 * k + (initial ∩ bridgeHighStock X (radii j)).card +
        2 * k * (overlappingBridgeWindows (Finset.range j)
          (fun i => bridgeHighStock X (radii i)) (bridgeHighStock X (radii j))).card ≤
      M + 2 * k + (initial ∩ bridgeHighStock X (radii j)).card +
        2 * k * (bridgeHighGeometricOverlap X radii j).card :=
      Nat.add_le_add_left hhiMul _
    have hreal : ((M + 2 * k + (initial ∩ bridgeHighStock X (radii j)).card +
        2 * k * (overlappingBridgeWindows (Finset.range j)
          (fun i => bridgeHighStock X (radii i)) (bridgeHighStock X (radii j))).card : ℕ) : ℝ) ≤
      ((M + 2 * k + (initial ∩ bridgeHighStock X (radii j)).card +
        2 * k * (bridgeHighGeometricOverlap X radii j).card : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact hreal.trans hbudgetHigh

/-- With the source's geometric budgets paid at every preterminal stage,
the complete finite sequence of mutually disjoint bridge batches exists. -/
theorem select_bridge_until_covered (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (initial : Finset ℕ) (R₀ : ℝ) (M : ℕ → ℕ) (k : ℕ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hR : 0 < R₀)
    (hbudget : ∀ j, bridgeIteration (poolMaximum n) R₀ j < poolMaximum n →
      bridgeGeometricStageBudget n initial (bridgeIteration (poolMaximum n) R₀) (M j) k j) :
    ∃ J : ℕ, ∃ batches : ℕ → List DoublePair,
      (poolMaximum n : ℝ) ≤ bridgeIteration (poolMaximum n) R₀ J ∧
      (∀ j < J, bridgeIteration (poolMaximum n) R₀ j < poolMaximum n) ∧
      (∀ j < J, bridgeStageValid n initial (bridgeIteration (poolMaximum n) R₀) batches k j) ∧
      (∀ i < J, ∀ j < J, i ≠ j →
        Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
          (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))) := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  obtain ⟨J, hstop, hbelow⟩ := bridgeIteration_terminates (poolMaximum n) R₀ hX hR
  have hpos : ∀ j < J, 0 < bridgeIteration (poolMaximum n) R₀ j := by
    intro j _
    exact bridgeIteration_pos (poolMaximum n) R₀ hX hR j
  have hactualBudget : ∀ j < J,
      bridgeStageBudget n initial (bridgeIteration (poolMaximum n) R₀) (M j) k j := by
    intro j hj
    apply bridgeStageBudget_of_geometric
    · intro i hi
      exact bridgeIteration_pos (poolMaximum n) R₀ hX hR i
    · exact hbudget j (hbelow j hj)
  obtain ⟨batches, hvalid⟩ := select_bridge_stage_sequence bmor upper n initial
    (bridgeIteration (poolMaximum n) R₀) M k J hn hnmax hpos hactualBudget
  exact ⟨J, batches, hstop, hbelow, hvalid,
    bridgeStageSequence_disjoint n initial (bridgeIteration (poolMaximum n) R₀) batches k J hvalid⟩
end
end Sude
