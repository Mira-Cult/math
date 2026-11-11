import Sude.FWMixedAffineActualIteration

/-! Fixed-wheel continuation at the actual selected-gap radius, with a
stage-indexed absolute mass and a fixed terminal mass. -/

namespace Sude
noncomputable section

/-- A fixed-wheel suffix recording the stage index and its absolute mass. -/
inductive FWMixedAffineVaryingSchedule (i : Fin 8) (n : ℕ) (L Mf eta : ℝ) (M : ℕ → ℝ) :
    ℕ → ℕ → ℕ → List BTSelectedStage → Prop
  | nil (j actual : ℕ) : FWMixedAffineVaryingSchedule i n L Mf eta M j actual actual []
  | cons (j actual actualFinal : ℕ) (stage : BTSelectedStage) (tail : List BTSelectedStage)
      (hbefore : (actual : ℝ) < (poolMaximum n : ℝ) / L)
      (hshift : 0 < (actual : ℝ) -
        fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta Mf)
      (hminimum : stage.minimum = fwAffineThreshold 2 (fwMixedWheelRho i) eta (M j) actual 1
        (poolMaximum n) (fwMixedWheelError i))
      (hpositive : 0 < stage.gap) (heven : 2 ∣ stage.gap)
      (hlower : fwAffineThreshold 2 (fwMixedWheelRho i) eta (M j) actual 1
        (poolMaximum n) (fwMixedWheelError i) ≤ stage.gap)
      (hgain : (fwAffineSlope eta 2 (M j) 1 (poolMaximum n) / fwMixedWheelRho i) *
        ((actual : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta Mf) ≤ stage.gap)
      (hupper : stage.gap ≤ actual)
      (hrest : FWMixedAffineVaryingSchedule i n L Mf eta M (j + 1)
        (actual + stage.gap) actualFinal tail) :
      FWMixedAffineVaryingSchedule i n L Mf eta M j actual actualFinal (stage :: tail)

/-- Iterate with each stage's own absolute stock lower bound. The drop between
adjacent mass bounds pays one exact pair-footprint depletion. -/
theorem fw_mixed_affine_varying_iterate_bounded (i : Fin 8) {n cap : ℕ}
    (fuel : ℕ) {initial S : Finset ℕ} {radius last j : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n + 8)) initial radius S last stages)
    (L Mf eta : ℝ) (M : ℕ → ℝ)
    (hlast : 0 < last) (heven : 2 ∣ last) (hL : 0 < L)
    (hS : S ⊆ (poolFinset n).filter (fun p => 43 < p))
    (heta : 0 < eta) (hMf : 0 < Mf)
    (heps : 0 ≤ 1 / (2 * (1 + 1 / L)) - eta)
    (hshift : 0 < (last : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1
      (poolMaximum n) eta Mf)
    (hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * poolMaximum n ≤
      (1 / (2 * (1 + 1 / L)) - eta) * Mf ^ 2)
    (hcap : j + fuel ≤ cap)
    (hmass : ∀ k < cap, Mf ≤ M k)
    (hslope : ∀ k < cap, fwAffineSlope eta 2 (M k) 1 (poolMaximum n) / fwMixedWheelRho i ≤ 1)
    (hdrop : ∀ k < cap, M (k + 1) + ((2 * (6 * (n + 8)) : ℕ) : ℝ) ≤ M k)
    (hstock : M j ≤ (S.card : ℝ)) :
    ∃ (final : Finset ℕ) (actualFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial radius final actualFinal (stages ++ extra) ∧
      extra.length ≤ fuel ∧ final ⊆ S ∧
      final.card + 2 * (6 * (n + 8)) * extra.length = S.card ∧
      M (j + extra.length) ≤ (final.card : ℝ) ∧
      ((poolMaximum n : ℝ) / L ≤ actualFinal ∨ extra.length = fuel) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      last ≤ actualFinal ∧ 2 ∣ actualFinal ∧
      FWMixedAffineVaryingSchedule i n L Mf eta M j last actualFinal extra := by
  induction fuel generalizing S last j stages with
  | zero =>
    refine ⟨S, last, [], ?_, by simp, Finset.Subset.rfl, by simp, ?_, ?_, ?_, le_rfl, heven,
      FWMixedAffineVaryingSchedule.nil _ _⟩
    · simpa using trace
    · simpa using hstock
    · right; simp
    · simp [NarrowedStages]
  | succ fuel ih =>
    by_cases hdone : (poolMaximum n : ℝ) / L ≤ last
    · refine ⟨S, last, [], ?_, by simp, Finset.Subset.rfl, by simp, ?_, ?_, ?_, le_rfl, heven,
        FWMixedAffineVaryingSchedule.nil _ _⟩
      · simpa using trace
      · simpa using hstock
      · exact Or.inl hdone
      · simp [NarrowedStages]
    · have hj : j < cap := by omega
      have hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / L := lt_of_not_ge hdone
      obtain ⟨hD, hDR, gap, chosen, hgap, hdiv, hmin, hgain, hmax, hcard,
        hpairs, hmatch, hfoot, hsize, hdeplete, hmid, hradius, htrace⟩ :=
        fw_mixed_affine_append_stage i trace L (M j) Mf eta hlast heven le_rfl hL
          (le_of_lt hnotdone) hS heta hMf (hmass j hj) hstock heps hshift (hslope j hj) hquota
      let D := fwAffineThreshold 2 (fwMixedWheelRho i) eta (M j) last 1 (poolMaximum n)
        (fwMixedWheelError i)
      let stage : BTSelectedStage := ⟨gap, chosen, D⟩
      have hlast' : 0 < last + gap := by omega
      have heven' : 2 ∣ last + gap := dvd_add heven hdiv
      have hS' : S \ pairFootprint chosen gap ⊆ (poolFinset n).filter (fun p => 43 < p) :=
        Finset.sdiff_subset.trans hS
      have hshift' : 0 < ((last + gap : ℕ) : ℝ) -
          fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta Mf := by
        push_cast
        have hgap0 : (0 : ℝ) ≤ gap := by positivity
        linarith
      have hdepleteR : ((S \ pairFootprint chosen gap).card : ℝ) +
          ((2 * (6 * (n + 8)) : ℕ) : ℝ) = S.card := by exact_mod_cast hdeplete
      have hstock' : M (j + 1) ≤ ((S \ pairFootprint chosen gap).card : ℝ) := by
        have hd := hdrop j hj
        linarith
      obtain ⟨final, actualFinal, extra, hfinal, hlen, hfinalSub, hfinalCard, hfinalStock,
        hstop, hnarrow, hgrows, hefinal, hsched⟩ :=
        ih htrace hlast' heven' hS' hshift' (by omega) hstock'
      refine ⟨final, actualFinal, stage :: extra, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hefinal, ?_⟩
      · simpa [stage, List.append_assoc] using hfinal
      · simpa using Nat.succ_le_succ hlen
      · exact hfinalSub.trans Finset.sdiff_subset
      · change final.card + (2 * (6 * (n + 8))) * (extra.length + 1) = S.card
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinalStock
      · rcases hstop with hs | hs
        · exact Or.inl hs
        · right; simpa using congrArg Nat.succ hs
      · intro s hs p hp q hq
        rcases List.mem_cons.mp hs with rfl | hs
        · simpa [stage] using hmid p hp q hq
        · exact hnarrow s hs p hp q hq
      · omega
      · exact FWMixedAffineVaryingSchedule.cons j last actualFinal stage extra hnotdone hshift
          rfl hgap hdiv hmin hgain hmax hsched


/-- Re-index the varying-mass continuation by the total number of existing
selected stages. The resulting stock and schedule use the exact global index. -/
theorem fw_mixed_affine_varying_global_iterate (i : Fin 8) {n cap : ℕ}
    (fuel : ℕ) {initial S : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n + 8)) initial radius S last stages)
    (L Mf eta : ℝ) (M : ℕ → ℝ)
    (hlast : 0 < last) (heven : 2 ∣ last) (hL : 0 < L)
    (hS : S ⊆ (poolFinset n).filter (fun p => 43 < p))
    (heta : 0 < eta) (hMf : 0 < Mf)
    (heps : 0 ≤ 1 / (2 * (1 + 1 / L)) - eta)
    (hshift : 0 < (last : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1
      (poolMaximum n) eta Mf)
    (hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * poolMaximum n ≤
      (1 / (2 * (1 + 1 / L)) - eta) * Mf ^ 2)
    (hcap : stages.length + fuel ≤ cap)
    (hmass : ∀ k < cap, Mf ≤ M k)
    (hslope : ∀ k < cap, fwAffineSlope eta 2 (M k) 1 (poolMaximum n) / fwMixedWheelRho i ≤ 1)
    (hdrop : ∀ k < cap, M (k + 1) + ((2 * (6 * (n + 8)) : ℕ) : ℝ) ≤ M k)
    (hstock : M stages.length ≤ (S.card : ℝ)) :
    ∃ (final : Finset ℕ) (actualFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial radius final actualFinal (stages ++ extra) ∧
      extra.length ≤ fuel ∧ final ⊆ S ∧
      final.card + 2 * (6 * (n + 8)) * extra.length = S.card ∧
      M (stages ++ extra).length ≤ (final.card : ℝ) ∧
      ((poolMaximum n : ℝ) / L ≤ actualFinal ∨ extra.length = fuel) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      last ≤ actualFinal ∧ 2 ∣ actualFinal ∧
      FWMixedAffineVaryingSchedule i n L Mf eta M stages.length last actualFinal extra := by
  obtain ⟨final, actualFinal, extra, htrace, hlen, hsub, hcard, hstock', hstop,
    hnarrow, hgrow, heven', hsched⟩ :=
    fw_mixed_affine_varying_iterate_bounded i fuel trace L Mf eta M hlast heven hL hS heta hMf
      heps hshift hquota hcap hmass hslope hdrop hstock
  refine ⟨final, actualFinal, extra, htrace, hlen, hsub, hcard, ?_, hstop,
    hnarrow, hgrow, heven', hsched⟩
  simpa using hstock'

end
end Sude
