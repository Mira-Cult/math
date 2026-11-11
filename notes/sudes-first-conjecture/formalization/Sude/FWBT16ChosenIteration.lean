import Sude.FWBT16ChosenTrace
import Sude.FWActualIndexRatio
import Sude.BTGrowingWidths

/-! Actual-radius BT16 iteration on the same screened early-witness trace.
The Montgomery--Vaughan hypothesis and the crossing-or-fuel alternative are explicit. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- Iterate actual selected BT16 stages without charging the 6Q candidate
matching: each appended stage retains Q pairs and deletes exactly 2Q values.
The width record uses global stage indices and actual accumulated radii. -/
theorem fw_bt16_chosen_iterate_first_band
    (mv : MVBrunTitchmarsh)
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (fuel : ℕ) (stock : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 stock last stages)
    (hbudget : stages.length + fuel ≤ 238) (hradius : 171331843 ≤ last) :
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    let width : ℕ → ℕ → ℝ := fun j R =>
      8 * ((3981035 / 10000000 : ℝ) * fwFirstBandMu j * R - 1 / 2)
    ∃ (final : Finset ℕ) (last' : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last' (stages ++ extra) ∧
      BTGrowingTrace 2 (6 * (n + 8)) stock last final last' extra ∧
      extra.length ≤ fuel ∧ stages.length + extra.length ≤ 238 ∧
      ((poolMaximum n : ℝ) / 23 ≤ last' ∨ extra.length = fuel) ∧
      BTWidthTrace width stages.length last extra ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      final ⊆ stock ∧ final.card + 2 * (6 * (n + 8)) * extra.length = stock.card ∧
      (stages ++ extra).Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) := by
  dsimp only
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  let width : ℕ → ℕ → ℝ := fun j R =>
    8 * ((3981035 / 10000000 : ℝ) * fwFirstBandMu j * R - 1 / 2)
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hratio := fw_actual_index_ratio bmor lower upper hnlo (by omega : n ≤ 35733)
  have hlog := fw_poolMaximum_log_gt_181_eighths lower hnlo
  have hQ := fw_first_band_stage_charge_from_fw3 hnlo hlog hratio
  have hreduced : ∀ a ∈ ({1} : Finset ℕ), 0 < a ∧ Nat.Coprime 2 a := by
    intro a ha
    have : a = 1 := by simpa using ha
    subst a
    decide
  have hrun : ∀ fuel : ℕ, ∀ (stock : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 stock last stages →
      stages.length + fuel ≤ 238 → 171331843 ≤ last →
      ∃ (final : Finset ℕ) (last' : ℕ) (extra : List BTSelectedStage),
        BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last' (stages ++ extra) ∧
        BTGrowingTrace 2 (6 * (n + 8)) stock last final last' extra ∧
        extra.length ≤ fuel ∧ stages.length + extra.length ≤ 238 ∧
        ((poolMaximum n : ℝ) / 23 ≤ last' ∨ extra.length = fuel) ∧
        BTWidthTrace width stages.length last extra ∧
        NarrowedStages ((poolMaximum n : ℝ) / 6) extra := by
    intro fuel
    induction fuel with
    | zero =>
      intro stock last stages trace hbudget hradius
      refine ⟨stock, last, [], ?_, BTGrowingTrace.nil _ _, by simp, ?_, ?_, BTWidthTrace.nil _ _, ?_⟩
      · simpa using trace
      · simpa using hbudget
      · right; simp
      · simp [NarrowedStages]
    | succ fuel ih =>
      intro stock last stages trace hbudget hradius
      by_cases hcross : (poolMaximum n : ℝ) / 23 ≤ last
      · refine ⟨stock, last, [], ?_, BTGrowingTrace.nil _ _, by simp, ?_, Or.inl hcross,
          BTWidthTrace.nil _ _, ?_⟩
        · simpa using trace
        · simpa using (show stages.length ≤ 238 by omega)
        · simp [NarrowedStages]
      · have hstock := (fw_first_band_varying_stock_mass bmor lower upper upperSharp hnlo hnhi
          batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last stock stages trace
          (by omega)).2
        have hstock' : fwFirstBandMu stages.length * (poolMaximum n : ℝ) ≤ (stock.card : ℝ) := by
          simpa only [fw_first_band_mu_mass] using hstock
        have hscreen : stock ⊆ (poolFinset n).filter (fun p => 43 < p) := by
          intro p hp
          exact (Finset.mem_sdiff.mp (trace.final_accounting.1 hp)).1
        have hunits := fw_screened_pool_mixed_wheel_units hscreen
        have hne : stock.Nonempty := by
          apply Finset.card_pos.mp
          have hmu := (fw_first_band_full_stock_quota_slack (j := stages.length) (by omega)).2.1
          have hpos : (0 : ℝ) < stock.card := lt_of_lt_of_le (mul_pos hmu hX) hstock'
          exact_mod_cast hpos
        have hprimes : ∀ p ∈ stock, Nat.Prime p := by
          intro p hp
          exact (pool_prime_and_residue (hunits p hp).1).1
        have hclasses : ∀ p ∈ stock, p % 2 ∈ ({1} : Finset ℕ) := by
          intro p hp
          simpa using (hunits p hp).2.2.1
        have hle : ∀ p ∈ stock, (p : ℝ) ≤ poolMaximum n := by
          intro p hp
          exact_mod_cast pool_le_poolMaximum (hunits p hp).1
        obtain ⟨gap, cands, chosen, hgap, hdiv, hupper, hlower, hcands, hcmatch, hcsub,
          hchoose, hchosen, hmatch, hfoot, hfootcard, hdeplete, hmid, htrace⟩ :=
          trace.append_fw_bt16_first_band mv (poolMaximum n) last {1} (by omega) hX hQ
            hradius le_rfl (le_of_lt (lt_of_not_ge hcross)) hstock' hne hprimes hclasses hreduced
            (by norm_num) hle
        let stage : BTSelectedStage := ⟨gap, chosen, width stages.length last⟩
        have htrace' : BTGrowingTrace 2 (6 * (n + 8)) initial 32
            (stock \ pairFootprint chosen gap) (last + gap) (stages ++ [stage]) := by
          exact htrace
        obtain ⟨final, last', extra, hfinal, hsuffix, hlen, htotal, hstop, hwidth, hnarrow⟩ :=
          ih (stock \ pairFootprint chosen gap) (last + gap) (stages ++ [stage]) htrace'
            (by simp; omega) (by omega)
        have hsuffix' : BTGrowingTrace 2 (6 * (n + 8)) stock last final last' (stage :: extra) := by
          exact BTGrowingTrace.cons stock last stage final last' extra hgap hdiv hupper hlower
            hchosen hmatch hfoot hsuffix
        refine ⟨final, last', stage :: extra, ?_, hsuffix', ?_, ?_, ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using hfinal
        · simpa using Nat.succ_le_succ hlen
        · simp only [List.length_cons, List.length_append] at htotal ⊢
          omega
        · rcases hstop with hcross' | hfull
          · exact Or.inl hcross'
          · right; simpa using congrArg Nat.succ hfull
        · apply BTWidthTrace.cons
          · rfl
          · simpa using hwidth
        · intro s hs p hp q hq
          rcases List.mem_cons.mp hs with rfl | hs
          · exact hmid p hp q hq
          · exact hnarrow s hs p hp q hq
  obtain ⟨final, last', extra, hfinal, hsuffix, hlen, htotal, hstop, hwidth, hnarrow⟩ :=
    hrun fuel stock last stages trace hbudget hradius
  have hacct := hsuffix.final_accounting
  refine ⟨final, last', extra, hfinal, hsuffix, hlen, htotal, hstop, hwidth, hnarrow,
    hacct.1, hacct.2.1, hfinal.pairwise_disjoint, ?_⟩
  intro stage hs
  apply Finset.disjoint_left.mpr
  intro p hp hearly
  have h := hsuffix.footprints_subset stage hs hp
  have hi := trace.final_accounting.1 h
  exact (Finset.mem_sdiff.mp hi).2 hearly

end
end Sude
