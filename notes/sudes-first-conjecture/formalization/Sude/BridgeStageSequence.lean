import Sude.BridgeDepletion

/-! Finite successive bridge-stage selection under explicit source budgets. -/
namespace Sude
noncomputable section

def bridgeStageBudget (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ)
    (M k j : ℕ) : Prop :=
  let X : ℝ := poolMaximum n
  let R := radii j
  ((M + 2 * k + (initial ∩ bridgeLowStock X R).card +
    2 * k * (overlappingBridgeWindows (Finset.range j)
      (fun i => bridgeLowStock X (radii i)) (bridgeLowStock X R)).card : ℕ) : ℝ) ≤
        bridgeStockBound X R ∧
  ((M + 2 * k + (initial ∩ bridgeHighStock X R).card +
    2 * k * (overlappingBridgeWindows (Finset.range j)
      (fun i => bridgeHighStock X (radii i)) (bridgeHighStock X R)).card : ℕ) : ℝ) ≤
        bridgeStockBound X R ∧
  bridgeWidth X R + 1 < (M : ℝ) * M

def bridgeStageValid (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ)
    (batches : ℕ → List DoublePair) (k j : ℕ) : Prop :=
  let X : ℝ := poolMaximum n
  let R := radii j
  let reserved := priorBridgeReservation initial (Finset.range j) batches
  (batches j).length = k ∧
    (∀ b ∈ batches j, b.valid (bridgeLowStock X R \ reserved)
      (bridgeHighStock X R \ reserved)) ∧
    (batches j).Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
    (∀ b ∈ batches j, 2 ∣ b.high₁ - b.low₁ ∧
      bridgeGapLower X R < ((b.high₁ - b.low₁ : ℕ) : ℝ) ∧
      ((b.high₁ - b.low₁ : ℕ) : ℝ) < bridgeSpan X R ∧
      ((b.high₁ - b.low₁ : ℕ) : ℝ) ≤ R)

theorem priorBridgeReservation_congr (initial active : Finset ℕ)
    (a b : ℕ → List DoublePair) (h : ∀ j ∈ active, a j = b j) :
    priorBridgeReservation initial active a = priorBridgeReservation initial active b := by
  unfold priorBridgeReservation stagedReservation
  congr 1
  apply Finset.biUnion_congr rfl
  intro j hj
  change doubleBatchLow (a j) ∪ doubleBatchHigh (a j) =
    doubleBatchLow (b j) ∪ doubleBatchHigh (b j)
  rw [h j hj]

/-- Every stage is selected using its actual accumulated reservation. The
source's protected-prefix, overlapping-window and current-stage charges are
explicit in `bridgeStageBudget`; none is assumed to be numerically true. -/
theorem select_bridge_stage_sequence (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ) (M : ℕ → ℕ) (k J : ℕ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hpositive : ∀ j < J, 0 < radii j)
    (hbudget : ∀ j < J, bridgeStageBudget n initial radii (M j) k j) :
    ∃ batches : ℕ → List DoublePair, ∀ j < J, bridgeStageValid n initial radii batches k j := by
  have hseq (t : ℕ) : t ≤ J → ∃ batches : ℕ → List DoublePair,
      ∀ j < t, bridgeStageValid n initial radii batches k j := by
    induction t with
    | zero =>
      intro _
      exact ⟨fun _ => [], by simp⟩
    | succ t ih =>
      intro ht
      have htJ : t < J := by omega
      obtain ⟨old, hold⟩ := ih (by omega)
      have hpriorR : ∀ j ∈ Finset.range t, 0 < radii j := by
        intro j hj
        exact hpositive j (by have := Finset.mem_range.mp hj; omega)
      have hpriorSize : ∀ j ∈ Finset.range t, (old j).length = k := by
        intro j hj
        exact (hold j (Finset.mem_range.mp hj)).1
      have hpriorValid : ∀ j ∈ Finset.range t, ∀ b ∈ old j,
          b.valid (bridgeLowStock (poolMaximum n) (radii j))
            (bridgeHighStock (poolMaximum n) (radii j)) := by
        intro j hj b hb
        have hv := (hold j (Finset.mem_range.mp hj)).2.1 b hb
        exact DoublePair.valid_mono hv Finset.sdiff_subset Finset.sdiff_subset
      have ⟨hlo, hhi, hgate⟩ := hbudget t htJ
      obtain ⟨chosen, hlen, hvalid, hpair, hgap⟩ :=
        bmor_bridge_stage_from_overlap_budget bmor upper n (radii t) initial (Finset.range t)
          radii old (M t) k hn hnmax (hpositive t htJ) hpriorR hpriorSize hpriorValid
          hlo hhi hgate
      let new : ℕ → List DoublePair := fun j => if j = t then chosen else old j
      have hnewOld : ∀ j < t, new j = old j := by
        intro j hj
        simp [new, Nat.ne_of_lt hj]
      have hreserve : ∀ j ≤ t,
          priorBridgeReservation initial (Finset.range j) new =
            priorBridgeReservation initial (Finset.range j) old := by
        intro j hj
        apply priorBridgeReservation_congr
        intro i hi
        exact hnewOld i (by have := Finset.mem_range.mp hi; omega)
      refine ⟨new, ?_⟩
      intro j hj
      by_cases hjt : j = t
      · subst j
        unfold bridgeStageValid
        rw [show new t = chosen by simp [new], hreserve t le_rfl]
        exact ⟨hlen, hvalid, hpair, hgap⟩
      · have hjlt : j < t := by omega
        unfold bridgeStageValid at *
        rw [hnewOld j hjlt, hreserve j (by omega)]
        exact hold j hjlt
  exact hseq J le_rfl

/-- Every entry of an earlier batch is included in the reservation seen by
any later stage. -/
theorem priorBridgeReservation_contains_batch (initial active : Finset ℕ)
    (batches : ℕ → List DoublePair) (j : ℕ) (hj : j ∈ active) :
    doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j) ⊆
      priorBridgeReservation initial active batches := by
  intro x hx
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨j, hj, hx⟩

/-- The stage invariant implies global disjointness of entries, including
the case of nonadjacent or overlapping bridge windows. -/
theorem bridgeStageSequence_disjoint (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ)
    (batches : ℕ → List DoublePair) (k J : ℕ)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j) :
    ∀ i < J, ∀ j < J, i ≠ j →
      Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
        (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j)) := by
  intro i hi j hj hne
  have hforward : ∀ a < J, ∀ b < J, a < b →
      Disjoint (doubleBatchLow (batches a) ∪ doubleBatchHigh (batches a))
        (doubleBatchLow (batches b) ∪ doubleBatchHigh (batches b)) := by
    intro a ha b hb hab
    have hv := (hvalid b hb).2.1
    have hdisj := doubleBatch_avoids_reservation (batches b)
      (bridgeLowStock (poolMaximum n) (radii b))
      (bridgeHighStock (poolMaximum n) (radii b))
      (priorBridgeReservation initial (Finset.range b) batches) hv
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hprior := priorBridgeReservation_contains_batch initial (Finset.range b) batches a
      (Finset.mem_range.mpr hab) hx
    exact Finset.disjoint_left.mp hdisj hy hprior
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hforward i hi j hj hlt
  · exact (hforward j hj i hi hgt).symm

end
end Sude
