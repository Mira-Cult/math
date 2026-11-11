import Sude.FWWheelFirstBandTrace

/-! A first wheel stage after the actual selected early values, starting with
the empty trace and radius 32. This does not construct a physical seed grid or
a later growth trace. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- At the seed radius the rational pre-floor expression is nonnegative but
less than one. The wheel cutoff is nevertheless positive: it counts a next
unit even when this floor is zero. -/
theorem fw_wheel_seed_radius_floor_zero :
    ⌊(3981035 / 10000000 : ℝ) * (403 / 10000 : ℝ) * 32 - 1 / 2⌋₊ = 0 := by
  norm_num

/-- The first two units of the wheel are 1 and 2, so the least distance
to the next unit is 1 when the window count is zero. -/
theorem fw_wheel_15015_zero_cutoff :
    fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) 0
      (Nat.totient_pos.mpr (by decide)) = 1 := by
  have h0 : fwWheelUnit 15015 0 = 1 := by
    have h := Nat.nth_count (show Nat.Coprime 15015 1 by decide)
    have hc : Nat.count (fun a : ℕ => Nat.Coprime 15015 a) 1 = 0 := by
      rw [Nat.count_eq_card_filter_range]
      decide
    simpa only [fwWheelUnit, hc] using h
  have h1 : fwWheelUnit 15015 1 = 2 := by
    have h := Nat.nth_count (show Nat.Coprime 15015 2 by decide)
    have hc : Nat.count (fun a : ℕ => Nat.Coprime 15015 a) 2 = 1 := by
      rw [Nat.count_eq_card_filter_range]
      decide
    simpa only [fwWheelUnit, hc] using h
  have hp := fw_wheel_cutoff_pos_of_pos 15015 0 (by decide)
  have hu := fw_wheel_cutoff_le_next (fwWheelUnit 15015) 15015 (Nat.totient 15015) 0
    (Nat.totient_pos.mpr (by decide)) (fw_wheel_unit_period 15015 (by decide))
    (fw_wheel_unit_strictMono 15015 (by decide)) 0
  simp only [Nat.zero_add, h1, h0] at hu
  omega

/-- The full even cutoff at radius 32 is exactly two. -/
theorem fw_wheel_seed_radius_cutoff_eq_two :
    let m : ℝ := 403 / 10000 - 2 * (1 / 69780 : ℝ) * ([] : List BTSelectedStage).length
    let T := ⌊(3981035 / 10000000 : ℝ) * m * 32 - 1 / 2⌋₊
    2 * min (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
      (Nat.totient_pos.mpr (by decide))) (32 / 2) = 2 := by
  dsimp only
  have hm : ((403 / 10000 : ℝ) - 2 * (1 / 69780 : ℝ) * ([] : List BTSelectedStage).length) =
      (403 / 10000 : ℝ) := by norm_num
  rw [hm, fw_wheel_seed_radius_floor_zero, fw_wheel_15015_zero_cutoff]
  norm_num

/-- The first-band append hypotheses hold for the empty trace with the
explicit auxiliary value V=23. The chosen stage uses the same supplied early
witnesses; its pair footprint is removed from the actual screened pool. -/
theorem fw_wheel_first_stage_from_seed_radius
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    let Q := 6 * (n + 8)
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    let m : ℝ := 403 / 10000 - 2 * (1 / 69780 : ℝ) * ([] : List BTSelectedStage).length
    let T := ⌊(3981035 / 10000000 : ℝ) * m * 32 - 1 / 2⌋₊
    let cutoff := 2 * min
      (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
        (Nat.totient_pos.mpr (by decide))) (32 / 2)
    ∃ (gap : ℕ) (chosen : Finset ℕ) (width : ℝ),
      width = (cutoff : ℝ) ∧ width = 2 ∧ 2 ≤ gap ∧ 2 ∣ gap ∧ cutoff ≤ gap ∧ gap ≤ 32 ∧
      chosen.card = Q ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ sameClassPairs initial (progressionBinKey 0 32 2)) ∧
      PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ initial ∧
      Disjoint (pairFootprint chosen gap)
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) ∧
      (pairFootprint chosen gap).card = 2 * Q ∧
      (initial \ pairFootprint chosen gap).card + 2 * Q = initial.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| <
          (poolMaximum n : ℝ) / 6) ∧
      32 + cutoff ≤ 32 + gap ∧
      BTGrowingTrace 2 Q initial 32 (initial \ pairFootprint chosen gap) (32 + gap)
        [⟨gap, chosen, width⟩] := by
  dsimp only
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  have hnotdone : (32 : ℝ) < (poolMaximum n : ℝ) / 23 := by
    have hX : (4 * 2 ^ 30 : ℝ) < (poolMaximum n : ℝ) := by
      exact_mod_cast fw_poolMaximum_gt_four_seed lower hnlo
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 23)).2
    norm_num at hX ⊢
    linarith
  have hA : 0 ≤ (3981035 / 10000000 : ℝ) *
      ((403 / 10000 : ℝ) - 2 * (1 / 69780 : ℝ) * ([] : List BTSelectedStage).length) * 32 - 1 / 2 := by
    norm_num
  have trace : BTGrowingTrace 2 (6 * (n + 8)) initial 32 initial 32 [] := BTGrowingTrace.nil initial 32
  obtain ⟨gap, chosen, hpos, heven, hcut, hgap, hcard', hpairs, hpairwise,
    hfoot, havoid, hsize, hacct, hmid, hgrowth, htrace⟩ :=
    fw_first_band_trace_first_window_append bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 32 initial [] trace
      (by simp) 23 (by norm_num) (by norm_num) 32 (by norm_num) (by norm_num) (by rfl) hnotdone hA
  refine ⟨gap, chosen, _, rfl, ?_, ?_, heven, hcut, hgap, hcard', hpairs, hpairwise, hfoot, havoid,
    hsize, hacct, hmid, hgrowth, htrace⟩
  · exact_mod_cast fw_wheel_seed_radius_cutoff_eq_two
  · omega

end
end Sude
