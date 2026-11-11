import Sude.FWWheelFirstBandFloor
import Sude.BTNarrowIteration

/-! An actual-radius first-window step for a supplied first-band trace.
No target coverage, trace existence, source recipe or physical placement is claimed. -/
namespace Sude
noncomputable section

/-- The supplied trace starts at 32; its final radius provides the positive,
even, floor-feasible WW5 radius. All other source assumptions remain explicit. -/
theorem fw_first_band_trace_first_window_append_at_last
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 final last stages)
    (hsteps : stages.length < 238)
    (hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / 23) :
    let Q := 6 * (n + 8)
    let m : ℝ := 403 / 10000 - 2 * (1 / 69780 : ℝ) * stages.length
    let T := ⌊(3981035 / 10000000 : ℝ) * m * last - 1 / 2⌋₊
    let cutoff := 2 * min
      (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
        (Nat.totient_pos.mpr (by decide))) (last / 2)
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ cutoff ≤ gap ∧ gap ≤ last ∧
      chosen.card = Q ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ sameClassPairs final (progressionBinKey 0 last 2)) ∧
      PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ final ∧
      Disjoint (pairFootprint chosen gap)
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) ∧
      (pairFootprint chosen gap).card = 2 * Q ∧
      (final \ pairFootprint chosen gap).card + 2 * Q = final.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| <
          (poolMaximum n : ℝ) / 6) ∧
      last + cutoff ≤ last + gap ∧
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 (final \ pairFootprint chosen gap) (last + gap)
        (stages ++ [⟨gap, chosen, (cutoff : ℝ)⟩]) := by
  have hr := fw_even_trace_radius_lower trace
  have hR : 0 < last := by omega
  have hA := (fw_first_band_floor_of_even_trace trace hsteps).2
  exact fw_first_band_trace_first_window_append_pointwise bmor lower upper upperSharp hnlo hnhi
    batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last final stages
    trace hsteps last hR hr.2 le_rfl hnotdone hA

/-- Starting from any supplied trace of at most 238 stages, iterate adaptive
first-wheel steps until the actual radius reaches X/23 or the 238-stage cap
is exhausted. Existing stages are retained as a prefix and every added stage
has midpoint spread below X/6. No crossing by the cap, frozen mixed recipe,
physical placement, or existence of the supplied initial witnesses is claimed. -/
theorem fw_first_band_trace_first_window_bounded_stop
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 final last stages) (hsteps : stages.length ≤ 238) :
    ∃ (final' : Finset ℕ) (last' : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8))
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final' last' (stages ++ extra) ∧
      (stages ++ extra).length ≤ 238 ∧
      ((poolMaximum n : ℝ) / 23 ≤ last' ∨ (stages ++ extra).length = 238) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra := by
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  have hrun : ∀ fuel : ℕ, ∀ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last stages →
      stages.length + fuel = 238 →
      ∃ (final' : Finset ℕ) (last' : ℕ) (extra : List BTSelectedStage),
        BTGrowingTrace 2 (6 * (n + 8)) initial 32 final' last' (stages ++ extra) ∧
        (stages ++ extra).length ≤ 238 ∧
        ((poolMaximum n : ℝ) / 23 ≤ last' ∨ (stages ++ extra).length = 238) ∧
        NarrowedStages ((poolMaximum n : ℝ) / 6) extra := by
    intro fuel
    induction fuel with
    | zero =>
      intro final last stages trace hlen
      refine ⟨final, last, [], ?_, ?_, ?_, ?_⟩
      · simpa using trace
      · simpa using (show stages.length ≤ 238 by omega)
      · right
        simpa using (show stages.length = 238 by omega)
      · simp [NarrowedStages]
    | succ fuel ih =>
      intro final last stages trace hlen
      by_cases hdone : (poolMaximum n : ℝ) / 23 ≤ last
      · refine ⟨final, last, [], ?_, ?_, ?_, ?_⟩
        · simpa using trace
        · simpa using (show stages.length ≤ 238 by omega)
        · exact Or.inl hdone
        · simp [NarrowedStages]
      · have hsteps' : stages.length < 238 := by omega
        have hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / 23 := lt_of_not_ge hdone
        let m : ℝ := 403 / 10000 - 2 * (1 / 69780 : ℝ) * stages.length
        let T : ℕ := ⌊(3981035 / 10000000 : ℝ) * m * last - 1 / 2⌋₊
        let cutoff : ℕ := 2 * min
          (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
            (Nat.totient_pos.mpr (by decide))) (last / 2)
        obtain ⟨gap, chosen, hgap, hdiv, hcut, hmax, hcard', hpairs, hmatch, hfoot,
          hav, hsize, hdepl, hmid, hradius, htrace⟩ :=
          fw_first_band_trace_first_window_append_at_last bmor lower upper upperSharp hnlo hnhi
            batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks last final stages
            (by simpa [initial] using trace) hsteps' hnotdone
        let stage : BTSelectedStage := ⟨gap, chosen, (cutoff : ℝ)⟩
        have htrace' : BTGrowingTrace 2 (6 * (n + 8)) initial 32
            (final \ pairFootprint chosen gap) (last + gap) (stages ++ [stage]) := by
          exact htrace
        have hlen' : (stages ++ [stage]).length + fuel = 238 := by simp; omega
        obtain ⟨final', last', extra, hfinal, hcap, hstop, hnarrow⟩ :=
          ih (final \ pairFootprint chosen gap) (last + gap) (stages ++ [stage]) htrace' hlen'
        refine ⟨final', last', stage :: extra, ?_, ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using hfinal
        · simpa [List.append_assoc] using hcap
        · simpa [List.append_assoc] using hstop
        · intro s hs p hp q hq
          rcases List.mem_cons.mp hs with rfl | hs
          · simpa [stage] using hmid p hp q hq
          · exact hnarrow s hs p hp q hq
  have hstart : stages.length + (238 - stages.length) = 238 := by omega
  simpa [initial] using hrun (238 - stages.length) final last stages trace hstart


/-- Starting from the empty trace after the supplied early reservation, an
adaptive first-wheel trace exists and either crosses X/23 or exhausts its
238-stage cap. Every retained stage has midpoint spread below X/6. This does
not prove the crossing alternative or source mixed-recipe fidelity. -/
theorem fw_first_band_first_window_trace_bounded_stop
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last stages ∧
      stages.length ≤ 238 ∧
      ((poolMaximum n : ℝ) / 23 ≤ last ∨ stages.length = 238) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages := by
  dsimp only
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  obtain ⟨final, last, extra, htrace, hcap, hstop, hnarrow⟩ :=
    fw_first_band_trace_first_window_bounded_stop bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 initial []
      (BTGrowingTrace.nil _ _) (by simp)
  exact ⟨final, last, extra, by simpa [initial] using htrace,
    by simpa using hcap, by simpa using hstop, hnarrow⟩


end
end Sude
