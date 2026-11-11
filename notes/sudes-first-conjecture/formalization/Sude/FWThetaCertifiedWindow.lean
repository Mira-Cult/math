import Sude.FWFirstWindowCertifiedRadius
import Sude.FWThetaFirstWindow

/-! The same certified first-window iteration from finite theta and RS
inputs. The early witnesses and starting trace remain supplied, and crossing
is an alternative, not a guaranteed conclusion. -/
namespace Sude
noncomputable section

/-- Append until actual crossing or the 118-step first-window phase cap. The
certified radius follows the WW cutoff recurrence and stays below actual
coverage. All starting witnesses and the trace remain explicit assumptions. -/
theorem fw_first_band_certified_first_window_bounded_stop_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (R last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 final last stages)
    (hsteps : stages.length ≤ 118) (hbound : 32 + 2 * stages.length ≤ R)
    (heven : 2 ∣ R) (hbelow : R ≤ last) :
    ∃ (final' : Finset ℕ) (R' last' : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8))
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final' last' (stages ++ extra) ∧
      (stages ++ extra).length ≤ 118 ∧
      ((poolMaximum n : ℝ) / 23 ≤ last' ∨ (stages ++ extra).length = 118) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      32 + 2 * (stages ++ extra).length ≤ R' ∧ 2 ∣ R' ∧ R' ≤ last' ∧
      FWFirstWindowCertifiedSchedule (poolMaximum n) stages.length R last R' last' extra := by
  obtain ⟨hVlo, hVhi⟩ := fw_first_band_pointwise_log_bounds upperSharp lower hnlo hnhi
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  have hrun : ∀ fuel : ℕ, ∀ (final : Finset ℕ) (R last : ℕ)
      (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last stages →
      stages.length + fuel = 118 → 32 + 2 * stages.length ≤ R →
      2 ∣ R → R ≤ last →
      ∃ (final' : Finset ℕ) (R' last' : ℕ) (extra : List BTSelectedStage),
        BTGrowingTrace 2 (6 * (n + 8)) initial 32 final' last' (stages ++ extra) ∧
        (stages ++ extra).length ≤ 118 ∧
        ((poolMaximum n : ℝ) / 23 ≤ last' ∨ (stages ++ extra).length = 118) ∧
        NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
        32 + 2 * (stages ++ extra).length ≤ R' ∧ 2 ∣ R' ∧ R' ≤ last' ∧
        FWFirstWindowCertifiedSchedule (poolMaximum n) stages.length R last R' last' extra := by
    intro fuel
    induction fuel with
    | zero =>
      intro final R last stages trace hlen hb he hl
      refine ⟨final, R, last, [], ?_, ?_, ?_, ?_, ?_, he, hl,
        FWFirstWindowCertifiedSchedule.nil _ _ _⟩
      · simpa using trace
      · simpa using (show stages.length ≤ 118 by omega)
      · right; simpa using (show stages.length = 118 by omega)
      · simp [NarrowedStages]
      · simpa using hb
    | succ fuel ih =>
      intro final R last stages trace hlen hb he hl
      by_cases hdone : (poolMaximum n : ℝ) / 23 ≤ last
      · refine ⟨final, R, last, [], ?_, ?_, ?_, ?_, ?_, he, hl,
          FWFirstWindowCertifiedSchedule.nil _ _ _⟩
        · simpa using trace
        · simpa using (show stages.length ≤ 118 by omega)
        · exact Or.inl hdone
        · simp [NarrowedStages]
        · simpa using hb
      · have hj : stages.length < 118 := by omega
        have hj238 : stages.length < 238 := by omega
        have hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / 23 := lt_of_not_ge hdone
        have hR : 0 < R := by omega
        have hfloor : 0 ≤ fwFirstWindowA stages.length R :=
          (fw_first_band_floor_of_radius hj238 hb).2
        let cutoff := fwFirstWindowCutoff stages.length R
        have hgeo : 0 < cutoff ∧ cutoff ≤ R ∧ 2 ∣ cutoff := by
          have h := fw_wheel_ww5_cutoff_geometry 15015 (fwFirstWindowT stages.length R)
            R (by decide) hR he
          exact ⟨h.1, h.2.1, h.2.2.1⟩
        have hcut2 : 2 ≤ cutoff := Nat.le_of_dvd hgeo.1 hgeo.2.2
        obtain ⟨gap, chosen, hgap, hdiv, hcut, hmax, hcard', hpairs, hmatch, hfoot,
          hav, hsize, hdepl, hmid, hradius, htrace⟩ :=
          fw_first_band_trace_first_window_append_of_theta bmor lower upper upperSharp hnlo hnhi
            batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last final stages
            (by simpa [initial] using trace) hj238 (Real.log (poolMaximum n : ℝ)) hVlo hVhi
            R hR he hl hnotdone hfloor
        let stage : BTSelectedStage := ⟨gap, chosen, (cutoff : ℝ)⟩
        have htrace' : BTGrowingTrace 2 (6 * (n + 8)) initial 32
            (final \ pairFootprint chosen gap) (last + gap) (stages ++ [stage]) := by
          exact htrace
        have hlen' : (stages ++ [stage]).length + fuel = 118 := by simp; omega
        have hb' : 32 + 2 * (stages ++ [stage]).length ≤ R + cutoff := by simp; omega
        have he' : 2 ∣ R + cutoff := dvd_add he hgeo.2.2
        have hl' : R + cutoff ≤ last + gap := by exact hradius
        obtain ⟨final', R', last', extra, hfinal, hcap, hstop, hnarrow,
          hbfinal, hefinal, hlfinal, hsched⟩ :=
          ih (final \ pairFootprint chosen gap) (R + cutoff) (last + gap)
            (stages ++ [stage]) htrace' hlen' hb' he' hl'
        refine ⟨final', R', last', stage :: extra, ?_, ?_, ?_, ?_, ?_, hefinal, hlfinal, ?_⟩
        · simpa [List.append_assoc] using hfinal
        · simpa [List.append_assoc] using hcap
        · simpa [List.append_assoc] using hstop
        · intro s hs p hp q hq
          rcases List.mem_cons.mp hs with rfl | hs
          · simpa [stage] using hmid p hp q hq
          · exact hnarrow s hs p hp q hq
        · simpa [List.append_assoc] using hbfinal
        · have hrest : FWFirstWindowCertifiedSchedule (poolMaximum n) (stages.length + 1)
              (R + fwFirstWindowCutoff stages.length R) (last + stage.gap) R' last' extra := by
            simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using hsched
          exact FWFirstWindowCertifiedSchedule.cons stages.length R last R' last' stage extra
            hj hnotdone hl hfloor rfl hgap hdiv hcut hmax hrest
  have hstart : stages.length + (118 - stages.length) = 118 := by omega
  simpa [initial] using hrun (118 - stages.length) final R last stages trace hstart hbound heven hbelow

end
end Sude
