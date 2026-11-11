import Sude.BridgeIteration

/-! FC2K same-side overlap accounting for successive bridge stages. -/
namespace Sude
noncomputable section

/-- Earlier windows that actually meet the current finite stock. -/
def overlappingBridgeWindows {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (active : Finset ι) (windows : ι → Finset α) (target : Finset α) : Finset ι :=
  active.filter fun j => ¬ Disjoint (windows j) target

/-- The initial reservation together with all entries selected at active stages. -/
def stagedReservation {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (initial : Finset α) (active : Finset ι) (low high : ι → Finset α) : Finset α :=
  initial ∪ active.biUnion (fun j => low j ∪ high j)

/-- Only stages whose same-side window meets the target can deplete it.
Opposite-side entries contribute nothing; overlaps among reservations are
charged at most once. -/
theorem stagedReservation_inter_card_le {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (initial target : Finset α) (active : Finset ι)
    (windows otherWindows low high : ι → Finset α) (Q : ℕ)
    (hlow : ∀ j ∈ active, low j ⊆ windows j)
    (hhigh : ∀ j ∈ active, high j ⊆ otherWindows j)
    (hcross : ∀ j ∈ active, Disjoint target (otherWindows j))
    (hcard : ∀ j ∈ active, (low j).card ≤ Q) :
    (stagedReservation initial active low high ∩ target).card ≤
      (initial ∩ target).card + Q * (overlappingBridgeWindows active windows target).card := by
  classical
  let overlapping := overlappingBridgeWindows active windows target
  have hsub : stagedReservation initial active low high ∩ target ⊆
      (initial ∩ target) ∪ overlapping.biUnion low := by
    intro x hx
    obtain ⟨hreserved, htarget⟩ := Finset.mem_inter.mp hx
    rcases Finset.mem_union.mp hreserved with hinit | hprior
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hinit, htarget⟩)
    · obtain ⟨j, hj, hentry⟩ := Finset.mem_biUnion.mp hprior
      rcases Finset.mem_union.mp hentry with hentry | hentry
      · have hmeet : ¬ Disjoint (windows j) target := by
          intro hdisj
          exact Finset.disjoint_left.mp hdisj (hlow j hj hentry) htarget
        have hj' : j ∈ overlapping := Finset.mem_filter.mpr ⟨hj, hmeet⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj', hentry⟩)
      · exact False.elim (Finset.disjoint_left.mp (hcross j hj) htarget (hhigh j hj hentry))
  have hunion : (overlapping.biUnion low).card ≤ overlapping.card * Q :=
    Finset.card_biUnion_le_card_mul overlapping low Q (by
      intro j hj
      exact hcard j (Finset.mem_filter.mp hj).1)
  calc
    (stagedReservation initial active low high ∩ target).card ≤
        ((initial ∩ target) ∪ overlapping.biUnion low).card := Finset.card_le_card hsub
    _ ≤ (initial ∩ target).card + (overlapping.biUnion low).card := Finset.card_union_le _ _
    _ ≤ (initial ∩ target).card + Q * overlapping.card := by
      simpa [Nat.mul_comm] using Nat.add_le_add_left hunion (initial ∩ target).card

/-- Every lower bridge stock lies strictly below X/2 and every upper stock
strictly above X/2, even for different stages. -/
theorem bridge_lower_upper_disjoint (X R S : ℝ) (hX : 0 < X) (hR : 0 < R) (hS : 0 < S) :
    Disjoint (bridgeLowStock X R) (bridgeHighStock X S) := by
  have hl := bridge_window_geometry X R hX hR
  have hu := bridge_window_geometry X S hX hS
  have hsl := bridgeSpan_properties X R hX hR
  have hsu := bridgeSpan_properties X S hX hS
  have hlowEnd : bridgeLowEnd X R < X / 2 := by
    simp only [bridgeLowEnd, bridgeLowStart, bridgeWidth]
    linarith [hsl.1]
  have hhighStart : X / 2 < bridgeHighStart X S := by
    simp only [bridgeHighStart, bridgeHighEnd, bridgeWidth]
    linarith [hsu.1]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' := (mem_apInterval_iff (bridgeLowStart X R) (bridgeLowEnd X R) 2 1
    (by linarith [hl.2.2.1]) (by linarith [hl.2.2.1, hl.2.2.2.1]) x).mp hx
  have hy' := (mem_apInterval_iff (bridgeHighStart X S) (bridgeHighEnd X S) 2 1
    (by linarith [hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1])
    (by linarith [hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2.1]) x).mp hy
  linarith [hx'.2.2.1, hy'.2.1]

/-- Distinct entries taken from each side by a batch of double pairs. -/
def doubleBatchLow (blocks : List DoublePair) : Finset ℕ :=
  blocks.toFinset.biUnion fun b => {b.low₁, b.low₂}

def doubleBatchHigh (blocks : List DoublePair) : Finset ℕ :=
  blocks.toFinset.biUnion fun b => {b.high₁, b.high₂}

theorem doubleBatchLow_card_le (blocks : List DoublePair) :
    (doubleBatchLow blocks).card ≤ 2 * blocks.length := by
  have hcard : ∀ b ∈ blocks.toFinset, ({b.low₁, b.low₂} : Finset ℕ).card ≤ 2 := by
    intro b _
    by_cases h : b.low₁ = b.low₂ <;> simp [h]
  have hu := Finset.card_biUnion_le_card_mul blocks.toFinset
    (fun b : DoublePair => ({b.low₁, b.low₂} : Finset ℕ)) 2 hcard
  have hl := List.toFinset_card_le blocks
  dsimp only [doubleBatchLow]
  nlinarith

theorem doubleBatchHigh_card_le (blocks : List DoublePair) :
    (doubleBatchHigh blocks).card ≤ 2 * blocks.length := by
  have hcard : ∀ b ∈ blocks.toFinset, ({b.high₁, b.high₂} : Finset ℕ).card ≤ 2 := by
    intro b _
    by_cases h : b.high₁ = b.high₂ <;> simp [h]
  have hu := Finset.card_biUnion_le_card_mul blocks.toFinset
    (fun b : DoublePair => ({b.high₁, b.high₂} : Finset ℕ)) 2 hcard
  have hl := List.toFinset_card_le blocks
  dsimp only [doubleBatchHigh]
  nlinarith

theorem doubleBatchLow_subset (blocks : List DoublePair) (low high : Finset ℕ)
    (hvalid : ∀ b ∈ blocks, b.valid low high) : doubleBatchLow blocks ⊆ low := by
  intro x hx
  obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.mp hx
  have hv := hvalid b (List.mem_toFinset.mp hb)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hv.1
  · exact hv.2.1

theorem doubleBatchHigh_subset (blocks : List DoublePair) (low high : Finset ℕ)
    (hvalid : ∀ b ∈ blocks, b.valid low high) : doubleBatchHigh blocks ⊆ high := by
  intro x hx
  obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.mp hx
  have hv := hvalid b (List.mem_toFinset.mp hb)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hv.2.2.1
  · exact hv.2.2.2.1

/-- A batch selected from the remaining stocks avoids every earlier
reservation, simultaneously on both sides. -/
theorem doubleBatch_avoids_reservation (blocks : List DoublePair) (low high reserved : Finset ℕ)
    (hvalid : ∀ b ∈ blocks, b.valid (low \ reserved) (high \ reserved)) :
    Disjoint (doubleBatchLow blocks ∪ doubleBatchHigh blocks) reserved := by
  apply Finset.disjoint_left.mpr
  intro x hx hr
  rcases Finset.mem_union.mp hx with hl | hh
  · exact (Finset.mem_sdiff.mp (doubleBatchLow_subset blocks _ _ hvalid hl)).2 hr
  · exact (Finset.mem_sdiff.mp (doubleBatchHigh_subset blocks _ _ hvalid hh)).2 hr

def priorBridgeReservation (initial : Finset ℕ) (active : Finset ℕ)
    (batches : ℕ → List DoublePair) : Finset ℕ :=
  stagedReservation initial active (fun j => doubleBatchLow (batches j))
    (fun j => doubleBatchHigh (batches j))

/-- One source bridge stage after arbitrary earlier stages. The explicit
budget charges protected entries and Q=2k for each overlapping earlier
same-side window, plus the whole current stage. No independence is assumed. -/
theorem bmor_bridge_stage_from_overlap_budget (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (R : ℝ) (initial active : Finset ℕ) (radii : ℕ → ℝ)
    (batches : ℕ → List DoublePair) (M k : ℕ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hR : 0 < R)
    (hpriorR : ∀ j ∈ active, 0 < radii j)
    (hpriorSize : ∀ j ∈ active, (batches j).length = k)
    (hpriorValid : ∀ j ∈ active, ∀ b ∈ batches j,
      b.valid (bridgeLowStock (poolMaximum n) (radii j))
        (bridgeHighStock (poolMaximum n) (radii j)))
    (hbudgetLow : ((M + 2 * k + (initial ∩ bridgeLowStock (poolMaximum n) R).card +
      2 * k * (overlappingBridgeWindows active
        (fun j => bridgeLowStock (poolMaximum n) (radii j))
        (bridgeLowStock (poolMaximum n) R)).card : ℕ) : ℝ) ≤
          bridgeStockBound (poolMaximum n) R)
    (hbudgetHigh : ((M + 2 * k + (initial ∩ bridgeHighStock (poolMaximum n) R).card +
      2 * k * (overlappingBridgeWindows active
        (fun j => bridgeHighStock (poolMaximum n) (radii j))
        (bridgeHighStock (poolMaximum n) R)).card : ℕ) : ℝ) ≤
          bridgeStockBound (poolMaximum n) R)
    (hgate : bridgeWidth (poolMaximum n) R + 1 < (M : ℝ) * M) :
    ∃ blocks : List DoublePair, blocks.length = k ∧
      (∀ b ∈ blocks, b.valid
        (bridgeLowStock (poolMaximum n) R \ priorBridgeReservation initial active batches)
        (bridgeHighStock (poolMaximum n) R \ priorBridgeReservation initial active batches)) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
      (∀ b ∈ blocks, 2 ∣ b.high₁ - b.low₁ ∧
        bridgeGapLower (poolMaximum n) R < ((b.high₁ - b.low₁ : ℕ) : ℝ) ∧
        ((b.high₁ - b.low₁ : ℕ) : ℝ) < bridgeSpan (poolMaximum n) R ∧
        ((b.high₁ - b.low₁ : ℕ) : ℝ) ≤ R) := by
  let X : ℝ := poolMaximum n
  let lw : ℕ → Finset ℕ := fun j => bridgeLowStock X (radii j)
  let hw : ℕ → Finset ℕ := fun j => bridgeHighStock X (radii j)
  let lo : ℕ → Finset ℕ := fun j => doubleBatchLow (batches j)
  let hi : ℕ → Finset ℕ := fun j => doubleBatchHigh (batches j)
  let targetLow := bridgeLowStock X R
  let targetHigh := bridgeHighStock X R
  let reserved := priorBridgeReservation initial active batches
  have hX : 0 < X := by
    change (0 : ℝ) < (poolMaximum n : ℝ)
    exact_mod_cast (poolMaximum_prime n).pos
  have hlow : ∀ j ∈ active, lo j ⊆ lw j := by
    intro j hj
    exact doubleBatchLow_subset (batches j) (lw j) (hw j) (hpriorValid j hj)
  have hhigh : ∀ j ∈ active, hi j ⊆ hw j := by
    intro j hj
    exact doubleBatchHigh_subset (batches j) (lw j) (hw j) (hpriorValid j hj)
  have hlowCard : ∀ j ∈ active, (lo j).card ≤ 2 * k := by
    intro j hj
    simpa [hpriorSize j hj] using doubleBatchLow_card_le (batches j)
  have hhighCard : ∀ j ∈ active, (hi j).card ≤ 2 * k := by
    intro j hj
    simpa [hpriorSize j hj] using doubleBatchHigh_card_le (batches j)
  have hcrossLow : ∀ j ∈ active, Disjoint targetLow (hw j) := by
    intro j hj
    exact bridge_lower_upper_disjoint X R (radii j) hX hR (hpriorR j hj)
  have hcrossHigh : ∀ j ∈ active, Disjoint targetHigh (lw j) := by
    intro j hj
    exact (bridge_lower_upper_disjoint X (radii j) R hX (hpriorR j hj) hR).symm
  have hreserve : reserved = stagedReservation initial active lo hi := rfl
  have hswap : stagedReservation initial active hi lo = stagedReservation initial active lo hi := by
    unfold stagedReservation
    congr 1
    apply Finset.biUnion_congr rfl
    intro j _
    exact Finset.union_comm _ _
  have hdepLow := stagedReservation_inter_card_le initial targetLow active lw hw lo hi (2 * k)
    hlow hhigh hcrossLow hlowCard
  have hdepHigh := stagedReservation_inter_card_le initial targetHigh active hw lw hi lo (2 * k)
    hhigh hlow hcrossHigh hhighCard
  rw [hswap, ← hreserve] at hdepHigh
  rw [← hreserve] at hdepLow
  have hneedLow : M + 2 * k + (targetLow ∩ reserved).card ≤
      M + 2 * k + (initial ∩ targetLow).card +
        2 * k * (overlappingBridgeWindows active lw targetLow).card := by
    rw [Finset.inter_comm targetLow reserved]
    omega
  have hneedHigh : M + 2 * k + (targetHigh ∩ reserved).card ≤
      M + 2 * k + (initial ∩ targetHigh).card +
        2 * k * (overlappingBridgeWindows active hw targetHigh).card := by
    rw [Finset.inter_comm targetHigh reserved]
    omega
  have hbudgetLow' : ((M + 2 * k + (targetLow ∩ reserved).card : ℕ) : ℝ) ≤
      bridgeStockBound X R := by
    have hc : ((M + 2 * k + (targetLow ∩ reserved).card : ℕ) : ℝ) ≤
        ((M + 2 * k + (initial ∩ targetLow).card +
          2 * k * (overlappingBridgeWindows active lw targetLow).card : ℕ) : ℝ) := by
      exact_mod_cast hneedLow
    exact hc.trans hbudgetLow
  have hbudgetHigh' : ((M + 2 * k + (targetHigh ∩ reserved).card : ℕ) : ℝ) ≤
      bridgeStockBound X R := by
    have hc : ((M + 2 * k + (targetHigh ∩ reserved).card : ℕ) : ℝ) ≤
        ((M + 2 * k + (initial ∩ targetHigh).card +
          2 * k * (overlappingBridgeWindows active hw targetHigh).card : ℕ) : ℝ) := by
      exact_mod_cast hneedHigh
    exact hc.trans hbudgetHigh
  exact bmor_bridge_select_pool_blocks bmor upper n R reserved M k hn hnmax hR
    hbudgetLow' hbudgetHigh' hgate

end
end Sude
