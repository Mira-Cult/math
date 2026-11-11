import Sude.FWBridgeFiveEmpty
import Sude.FWNarrowReservation

/-! Exact selected FW bridge values and conditional retained-seed selection. -/
namespace Sude
noncomputable section

/-- Every endpoint in the empty-initial five-stage FW bridge reservation is
an actual pool entry at least `X/4`. This uses supplied valid batches and the
explicit published BMOR and RS upper hypotheses; it does not construct the
batches or claim any physical placement. -/
theorem fw_selected_bridge_values_pool_and_quarter
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (n : ℕ)
    (batches : ℕ → List DoublePair)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j) :
    ∀ p ∈ priorBridgeReservation ∅ (Finset.range 5) batches,
      p ∈ poolFinset n ∧ poolMaximum n ≤ 4 * p := by
  let X : ℝ := poolMaximum n
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  intro p hp
  simp only [priorBridgeReservation, stagedReservation, Finset.empty_union,
    Finset.mem_biUnion, Finset.mem_range] at hp
  obtain ⟨j, hj, hp⟩ := hp
  have hstage := (hvalid j hj).1
  have hvalid' : ∀ b ∈ batches j,
      b.valid (fwBridgeLowStock X (fwBridgeRadius X j))
        (fwBridgeHighStock X (fwBridgeRadius X j)) := by
    intro b hb
    exact DoublePair.valid_mono (hstage.2.1 b hb) Finset.sdiff_subset Finset.sdiff_subset
  have hR := fw_bridge_nominal_radius_pos X hX j hj
  have hgeom := fw_bridge_window_geometry X (fwBridgeRadius X j) hX hR
  have hstock := bmor_fw_bridge_stocks bmor upper n (fwBridgeRadius X j) hn hnmax hR
  rcases Finset.mem_union.mp hp with hpLow | hpHigh
  · have hmem := doubleBatchLow_subset (batches j) _ _ hvalid' hpLow
    have hprime := hstock.2.2.1 p hmem
    have hw := (mem_apInterval_iff _ _ 2 1 (by linarith [hgeom.2.2.1])
      (by linarith [hgeom.2.2.1, hgeom.2.2.2.1]) p).mp hmem
    have hquarter : X ≤ 4 * (p : ℝ) := by linarith [hgeom.2.2.1, hw.2.1]
    exact ⟨mem_poolFinset.mpr hprime, by dsimp [X] at hquarter; exact_mod_cast hquarter⟩
  · have hmem := doubleBatchHigh_subset (batches j) _ _ hvalid' hpHigh
    have hprime := hstock.2.2.2 p hmem
    have hw := (mem_apInterval_iff _ _ 2 1
      (by linarith [hgeom.2.2.1, hgeom.2.2.2.1, hgeom.2.2.2.2.1])
      (by linarith [hgeom.2.2.1, hgeom.2.2.2.1, hgeom.2.2.2.2.1, hgeom.2.2.2.2.2.1]) p).mp hmem
    have hquarter : X ≤ 4 * (p : ℝ) := by
      linarith [hgeom.2.2.1, hgeom.2.2.2.1, hgeom.2.2.2.2.1, hw.2.1]
    exact ⟨mem_poolFinset.mpr hprime, by dsimp [X] at hquarter; exact_mod_cast hquarter⟩

/-- Conditional on the actual FT-sized twin-prime population, choose the
five source bridge batches first and then retain the source's sixteen narrow
seed groups in the exact remaining pool. The numerical FT population, any
physical geometry, growth stages and complete route remain open. -/
theorem bmor_fw_bridges_then_narrow_seeds
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 3650551 ≤ seeds.card) :
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
    fw_actual_narrow_seed_reservation lower n seeds
      (priorBridgeReservation ∅ (Finset.range 5) batches) hnlo hnhi hseed hprime
      (fun p hp => (hbridge p hp).2) hcount
  exact ⟨batches, hvalid, hpair, hcardBridge, hbridge, candidates, hcard, hcand,
    kept, hsub, hkept, hvariance, hreservation⟩

end
end Sude
