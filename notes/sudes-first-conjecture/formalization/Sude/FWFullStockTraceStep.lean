import Sude.FWFirstBandFullStockNonnegative
import Sude.FWFirstBandVaryingAffine
import Sude.FWWheelFirstBandFloor

/-! One first-band full-stock affine selection and actual-radius trace append.
The same early witnesses and supplied trace are retained. This does not prove
that the wheel-origin condition holds, that the trace exists, or that any
subsequent stage crosses the target. -/
namespace Sude
noncomputable section

/-- Narrow a freshly selected full-stock matching to Q pairs, label the stage
with the original source threshold, and advance by its actual selected gap.
The selected gap also clears that threshold's even ceiling by two. -/
theorem fw_full_stock_append_stage (i : Fin 8)
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 final last stages)
    (hsteps : stages.length < 238) (hlast : 11648 ≤ last)
    (hbefore : (last : ℝ) < (poolMaximum n : ℝ) / 23)
    (hshift : 0 < (last : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n)) :
    let X : ℝ := poolMaximum n
    let Q := 6 * (n + 8)
    let mu := fwFirstBandMu stages.length
    let D := fwAffineUniformStockThreshold mu (6 / 69780) last (23 / 48)
      (fwMixedWheelRho i) (fwMixedWheelError i)
    let Dsource := fwAffineThreshold 2 (fwMixedWheelRho i) (3981035 / 10000000)
      (mu * X) last 1 X (fwMixedWheelError i)
    0 < Dsource ∧ Dsource ≤ last ∧
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ D ≤ gap ∧ Dsource < gap ∧
      2 * ⌈Dsource / 2⌉₊ + 2 ≤ gap ∧ gap ≤ last ∧ chosen.card = Q ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ sameClassPairs final (progressionBinKey 0 last 2)) ∧
      PairwiseDisjointPairs chosen gap ∧ pairFootprint chosen gap ⊆ final ∧
      Disjoint (pairFootprint chosen gap)
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) ∧
      (pairFootprint chosen gap).card = 2 * Q ∧
      (final \ pairFootprint chosen gap).card + 2 * Q = final.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + gap : ℕ)) / 2) - (((q : ℝ) + (q + gap : ℕ)) / 2)| < X / 6) ∧
      (fwAffineSlope (3981035 / 10000000) 2 (mu * X) 1 X / fwMixedWheelRho i) *
        ((last : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 X
          (3981035 / 10000000) ((3257 / 100000 : ℝ) * X)) ≤ gap ∧
      BTGrowingTrace 2 Q
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 (final \ pairFootprint chosen gap) (last + gap)
        (stages ++ [⟨gap, chosen, Dsource⟩]) := by
  dsimp only
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have heven : 2 ∣ last := (fw_even_trace_radius_lower trace).2
  have hMf : (0 : ℝ) < (3257 / 100000 : ℝ) * poolMaximum n := by positivity
  have hmass : (3257 / 100000 : ℝ) * poolMaximum n ≤
      fwFirstBandMu stages.length * poolMaximum n := by
    simpa only [← fw_first_band_mu_mass] using
      (fw_varying_mass_floor_238 hX.le (show stages.length ≤ 238 by omega))
  have hslope : fwAffineSlope (3981035 / 10000000) 2
      (fwFirstBandMu stages.length * poolMaximum n) 1 (poolMaximum n) / fwMixedWheelRho i ≤ 1 := by
    simpa only [fwFirstBandMu] using fw_varying_mass_slope i hX stages.length
  have hC : 0 ≤ fwMixedWheelError i :=
    fw_affine_discrepancy_nonneg (fw_mixed_wheel_affine_discrepancy i)
  have hbounds := fw_affine_threshold_bounds (g := 2) (rho := fwMixedWheelRho i)
    (eta := (3981035 / 10000000 : ℝ))
    (M := fwFirstBandMu stages.length * poolMaximum n) (R := (last : ℝ))
    (r := 1) (X := (poolMaximum n : ℝ)) (C := fwMixedWheelError i)
    (Mf := (3257 / 100000 : ℝ) * poolMaximum n)
    (by norm_num) (fw_mixed_wheel_rho_pos i) (by norm_num) (by norm_num) hX hC hMf hmass hshift hslope
  obtain ⟨gap, allPairs, hgap, hdiv, hD, hDsource, hinc, hmax, hcount,
    hpairs, havail, hfoot, hdisj, hmatch⟩ :=
    fw_first_band_full_stock_witness_gap_above_increment_of_source_nonneg i
      bmor lower upper upperSharp hnlo hnhi batches hvalid candidates hcard kept hsub hkept hinj
      blocks hblocks 32 last last final stages trace (by omega) hlast heven hbefore.le hbounds.1.le
  have hspan : ∀ p ∈ allPairs, (0 : ℝ) ≤ p ∧
      (p : ℝ) < 0 + (6 : ℕ) * ((poolMaximum n : ℝ) / 6) := by
    intro p hp
    have hpnext : p + gap ∈ final := (havail p hp).2
    have hpool := trace.final_accounting.1 hpnext
    have hpPool : p + gap ∈ pool n := mem_poolFinset.mp ((Finset.mem_filter.mp (Finset.mem_sdiff.mp hpool).1).1)
    have hbound : ((p + gap : ℕ) : ℝ) ≤ poolMaximum n := by exact_mod_cast pool_le_poolMaximum hpPool
    have hgap' : (0 : ℝ) < (gap : ℝ) := by exact_mod_cast hgap
    push_cast at hbound
    constructor <;> linarith
  obtain ⟨chosen, hchosenSub, hcard', hmatch', hfoot', hsize, hdeplete, hmid, htrace⟩ :=
    trace.append_narrow_matching (z := 6) allPairs gap
      (fwAffineThreshold 2 (fwMixedWheelRho i) (3981035 / 10000000)
        (fwFirstBandMu stages.length * poolMaximum n) last 1 (poolMaximum n) (fwMixedWheelError i))
      0 ((poolMaximum n : ℝ) / 6)
      hgap hdiv hmax hDsource.le (by norm_num) (by positivity)
      hspan hcount hmatch hfoot
  have hchosenFoot : pairFootprint chosen gap ⊆ pairFootprint allPairs gap := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Finset.mem_union_left _ (hchosenSub hp)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hchosenSub hq, rfl⟩)
  have hdisj' : Disjoint (pairFootprint chosen gap)
      (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) :=
    hdisj.mono_left hchosenFoot
  refine ⟨hbounds.1, hbounds.2.1, gap, chosen, hgap, hdiv, hD, hDsource, hinc, hmax,
    hcard', ?_, hmatch', hfoot', hdisj', hsize, hdeplete, hmid, ?_, htrace⟩
  · intro p hp
    exact hpairs p (hchosenSub hp)
  · exact hbounds.2.2.trans hDsource.le

end
end Sude
