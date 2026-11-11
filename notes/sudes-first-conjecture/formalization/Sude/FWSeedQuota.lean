import Sude.FWBridgeSeedIntegration

/-! FW seed and bridge selection under the exact needed candidate quota.

The older stronger `3650551` interfaces remain unchanged. These theorems
replace only that population premise by `6*(n+8)*(16+2-1) ≤ seeds.card`;
they do not prove this quota or alter the seed, bridge or geometry conditions.
-/
namespace Sude
noncomputable section

/-- Select the exact candidate quota from a supplied matching. -/
theorem fw_seed_candidates_after_bridges_of_quota
    (pool seeds bridges : Finset ℕ) (n X : ℕ)
    (_hn : n ≤ 35733) (hsep : 4 * 2 ^ 30 < X)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hbridge : ∀ p ∈ bridges, X ≤ 4 * p)
    (hpool : ∀ p ∈ seeds, p ∈ pool ∧ p + 2 ∈ pool)
    (hmatch : PairwiseDisjointPairs seeds 2)
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    ∃ candidates : Finset ℕ,
      candidates ⊆ seeds ∧ candidates.card = 6 * (n + 8) * (16 + 2 - 1) ∧
      PairwiseDisjointPairs candidates 2 ∧
      pairFootprint candidates 2 ⊆ pool \ bridges ∧
      (pairFootprint candidates 2).card = 2 * (6 * (n + 8) * (16 + 2 - 1)) := by
  classical
  obtain ⟨candidates, hsub, hcard⟩ := Finset.exists_subset_card_eq hcount
  have hm : PairwiseDisjointPairs candidates 2 := by
    intro p hp q hq hpq
    exact hmatch p (hsub hp) q (hsub hq) hpq
  have hdis := fw_seed_bridge_disjoint seeds bridges (2 ^ 30) X hsep hseed hbridge
  have hsubset : pairFootprint candidates 2 ⊆ pool \ bridges := by
    intro p hp
    have hpSeed : p ∈ pairFootprint seeds 2 := by
      rcases Finset.mem_union.mp hp with hl | hu
      · exact Finset.mem_union_left _ (hsub hl)
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hsub hq, rfl⟩)
    have hpPool : p ∈ pool := by
      rcases Finset.mem_union.mp hp with hl | hu
      · exact (hpool p (hsub hl)).1
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
        exact (hpool q (hsub hq)).2
    exact Finset.mem_sdiff.mpr ⟨hpPool, (Finset.disjoint_left.mp hdis) hpSeed⟩
  refine ⟨candidates, hsub, hcard, hm, hsubset, ?_⟩
  rw [pairFootprint_card candidates 2 (by decide) hm, hcard]


/-- The exact quota applies to the actual prescribed-pool seed matching. -/
theorem fw_actual_seed_candidates_after_bridges_of_quota (lower : RSIndexLower)
    (n : ℕ) (seeds bridges : Finset ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hbridge : ∀ p ∈ bridges, poolMaximum n ≤ 4 * p)
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    ∃ candidates : Finset ℕ,
      candidates ⊆ seeds ∧ candidates.card = 6 * (n + 8) * (16 + 2 - 1) ∧
      PairwiseDisjointPairs candidates 2 ∧
      pairFootprint candidates 2 ⊆ poolFinset n \ bridges ∧
      (pairFootprint candidates 2).card = 2 * (6 * (n + 8) * (16 + 2 - 1)) := by
  have hmax := fw_poolMaximum_gt_four_seed lower hnlo
  have hpool : ∀ p ∈ seeds, p ∈ poolFinset n ∧ p + 2 ∈ poolFinset n := by
    intro p hp
    obtain ⟨hbig, hpprime, hqprime⟩ := hprime p hp
    have hbound := hseed p hp
    constructor <;> apply mem_poolFinset.mpr
    · exact prime_mem_pool_of_le_max hpprime (by omega) (by omega)
    · exact prime_mem_pool_of_le_max hqprime (by omega) (by omega)
  have hmatch : PairwiseDisjointPairs seeds 2 := by
    apply binary_prime_family_disjoint seeds 1
    intro p hp
    obtain ⟨hbig, hpprime, hqprime⟩ := hprime p hp
    simpa using (show 3 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2) from ⟨by omega, hpprime, hqprime⟩)
  exact fw_seed_candidates_after_bridges_of_quota (poolFinset n) seeds bridges n (poolMaximum n)
    hnhi hmax hseed hbridge hpool hmatch hcount


/-- Narrow the quota into the same sixteen retained groups and variance bound. -/
theorem fw_actual_narrow_seed_of_quota (lower : RSIndexLower) (n : ℕ)
    (seeds bridges : Finset ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hbridge : ∀ p ∈ bridges, poolMaximum n ≤ 4 * p)
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let Q := 6 * (n + 8)
    let r := 16 + 2 - 1
    ∃ (candidates : Finset ℕ) (hcard : candidates.card = r * Q),
      candidates ⊆ seeds ∧
      let w := sortedSeedReal candidates r Q hcard
      ∃ kept : Finset ℕ, kept ⊆ Finset.range r ∧ kept.card = 16 ∧
        (∃ z : ℝ, (∃ i ∈ kept, z = w (i * Q + (Q - 1)) - w (i * Q)) ∧
          (∀ i ∈ kept, w (i * Q + (Q - 1)) - w (i * Q) ≤ z) ∧
          3 * 6 * (∑ i ∈ kept, (w (i * Q + (Q - 1)) - w (i * Q)) ^ 2) + 4 * z ^ 2 ≤
            (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) ∧
        Function.Injective (sortedSeedEndpoint candidates r Q 2 hcard) ∧
        ∀ x, sortedSeedEndpoint candidates r Q 2 hcard x ∈ poolFinset n \ bridges := by
  dsimp only
  let Q := 6 * (n + 8)
  let r := 16 + 2 - 1
  obtain ⟨candidates, hsub, hcard0, hmatch, hav, _⟩ :=
    fw_actual_seed_candidates_after_bridges_of_quota lower n seeds bridges hnlo hnhi
      hseed hprime hbridge hcount
  have hcard : candidates.card = r * Q := by simpa [r, Q, Nat.mul_comm] using hcard0
  have hQ : 0 < Q := by dsimp [Q]; omega
  have hB : ∀ p ∈ candidates, p ≤ 2 ^ 30 := by
    intro p hp
    have h := hseed p (hsub hp)
    omega
  have hv := sortedSeedCandidates_variance candidates (poolFinset n) bridges Q 16 2 2
    (2 ^ 30) 6 hQ (by decide) (by decide) (by decide) (by norm_num)
    hcard hB hmatch hav
  refine ⟨candidates, hcard, hsub, ?_⟩
  norm_num at hv ⊢
  exact hv


/-- The retained endpoint reservation has the same count and availability. -/
theorem fw_actual_narrow_seed_reservation_of_quota (lower : RSIndexLower) (n : ℕ)
    (seeds bridges : Finset ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hbridge : ∀ p ∈ bridges, poolMaximum n ≤ 4 * p)
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let Q := 6 * (n + 8)
    let r := 16 + 2 - 1
    ∃ (candidates : Finset ℕ) (hcard : candidates.card = r * Q),
      candidates ⊆ seeds ∧
      ∃ (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r), kept.card = 16 ∧
        (let w := sortedSeedReal candidates r Q hcard
         ∃ z : ℝ, (∃ i ∈ kept, z = w (i * Q + (Q - 1)) - w (i * Q)) ∧
          (∀ i ∈ kept, w (i * Q + (Q - 1)) - w (i * Q) ≤ z) ∧
          3 * 6 * (∑ i ∈ kept, (w (i * Q + (Q - 1)) - w (i * Q)) ^ 2) + 4 * z ^ 2 ≤
            (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) ∧
        (let R := retainedSeedEndpoints candidates r Q 2 hcard kept hsub
         R.card = 2 * Q * 16 ∧ R ⊆ poolFinset n \ bridges ∧
         ∀ x, x.1.1.val ∉ kept →
           sortedSeedEndpoint candidates r Q 2 hcard x ∈ poolFinset n \ (bridges ∪ R)) := by
  dsimp only
  let Q := 6 * (n + 8)
  let r := 16 + 2 - 1
  obtain ⟨candidates, hcard, hcand, kept, hsub, hkept, hvariance, hinj, havail⟩ :=
    fw_actual_narrow_seed_of_quota lower n seeds bridges hnlo hnhi hseed hprime hbridge hcount
  refine ⟨candidates, hcard, hcand, kept, hsub, hkept, hvariance, ?_⟩
  let R := retainedSeedEndpoints candidates r Q 2 hcard kept hsub
  have hRcard : R.card = 2 * Q * 16 := by
    dsimp [R, retainedSeedEndpoints]
    rw [Finset.card_image_of_injective _ hinj, retainedSeedLabels_card, hkept]
  have hRsub : R ⊆ poolFinset n \ bridges := by
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact havail x
  refine ⟨hRcard, hRsub, ?_⟩
  intro x hdiscard
  have hx := Finset.mem_sdiff.mp (havail x)
  have hnot := discardedSeedEndpoint_not_retained candidates r Q 2 hcard hinj kept hsub x hdiscard
  refine Finset.mem_sdiff.mpr ⟨hx.1, ?_⟩
  intro hm
  rcases Finset.mem_union.mp hm with hb | hret
  · exact hx.2 hb
  · exact hnot hret


/-- Select the same five bridges and retained seeds from the exact quota. -/
theorem bmor_fw_bridges_then_narrow_seeds_of_quota
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let Q := 6 * (n + 8)
    let r := 16 + 2 - 1
    ∃ batches : ℕ → List DoublePair,
      (∀ j < 5, FWBridgeSequentialValid n ∅ batches j) ∧
      (∀ i < 5, ∀ j < 5, i ≠ j →
        Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
          (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))) ∧
      (∀ j ≤ 5, (priorBridgeReservation ∅ (Finset.range j) batches).card ≤
        (∅ : Finset ℕ).card + j * (4 * (3 * (n + 8)))) ∧
      (∀ p ∈ priorBridgeReservation ∅ (Finset.range 5) batches,
        p ∈ poolFinset n ∧ poolMaximum n ≤ 4 * p) ∧
      ∃ (candidates : Finset ℕ) (hcard : candidates.card = r * Q),
        candidates ⊆ seeds ∧
        ∃ (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r), kept.card = 16 ∧
          (let w := sortedSeedReal candidates r Q hcard
           ∃ z : ℝ, (∃ i ∈ kept, z = w (i * Q + (Q - 1)) - w (i * Q)) ∧
            (∀ i ∈ kept, w (i * Q + (Q - 1)) - w (i * Q) ≤ z) ∧
            3 * 6 * (∑ i ∈ kept, (w (i * Q + (Q - 1)) - w (i * Q)) ^ 2) + 4 * z ^ 2 ≤
              (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) ∧
          (let B := priorBridgeReservation ∅ (Finset.range 5) batches
           let R := retainedSeedEndpoints candidates r Q 2 hcard kept hsub
           R.card = 2 * Q * 16 ∧ R ⊆ poolFinset n \ B ∧
           ∀ x, x.1.1.val ∉ kept →
             sortedSeedEndpoint candidates r Q 2 hcard x ∈ poolFinset n \ (B ∪ R)) := by
  dsimp only
  obtain ⟨batches, hvalid, hpair, hcardBridge⟩ :=
    bmor_fw_five_bridge_batches_empty bmor upper lower hnlo hnhi
  have hbridge := fw_selected_bridge_values_pool_and_quarter bmor upper n batches (by omega) (by omega) hvalid
  obtain ⟨candidates, hcard, hcand, kept, hsub, hkept, hvariance, hreservation⟩ :=
    fw_actual_narrow_seed_reservation_of_quota lower n seeds
      (priorBridgeReservation ∅ (Finset.range 5) batches) hnlo hnhi hseed hprime
      (fun p hp => (hbridge p hp).2) hcount
  exact ⟨batches, hvalid, hpair, hcardBridge, hbridge, candidates, hcard, hcand,
    kept, hsub, hkept, hvariance, hreservation⟩


end
end Sude
