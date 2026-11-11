import Sude.FWMixedAffineIteration

/-! Fixed-wheel affine continuation using each stage's actual selected gap as
its next radius. All analytic, stock and initial-trace hypotheses are retained;
no crossing, frozen mixed recipe or physical placement is asserted. -/
namespace Sude
noncomputable section

/-- A source-threshold-labeled affine suffix. Each stage is chosen at its
actual current radius and the following radius is exactly that radius plus
the selected gap, so any surplus is carried into subsequent stages. -/
inductive FWMixedAffineActualSchedule (i : Fin 8) (n : ℕ) (L M Mf eta : ℝ) :
    ℕ → ℕ → List BTSelectedStage → Prop
  | nil (actual : ℕ) : FWMixedAffineActualSchedule i n L M Mf eta actual actual []
  | cons (actual actualFinal : ℕ) (stage : BTSelectedStage) (tail : List BTSelectedStage)
      (hbefore : (actual : ℝ) < (poolMaximum n : ℝ) / L)
      (hshift : 0 < (actual : ℝ) -
        fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta Mf)
      (hminimum : stage.minimum = fwAffineThreshold 2 (fwMixedWheelRho i) eta M actual 1
        (poolMaximum n) (fwMixedWheelError i))
      (hpositive : 0 < stage.gap) (heven : 2 ∣ stage.gap)
      (hlower : fwAffineThreshold 2 (fwMixedWheelRho i) eta M actual 1
        (poolMaximum n) (fwMixedWheelError i) ≤ stage.gap)
      (hgain : (fwAffineSlope eta 2 M 1 (poolMaximum n) / fwMixedWheelRho i) *
        ((actual : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta Mf) ≤ stage.gap)
      (hupper : stage.gap ≤ actual)
      (hrest : FWMixedAffineActualSchedule i n L M Mf eta (actual + stage.gap) actualFinal tail) :
      FWMixedAffineActualSchedule i n L M Mf eta actual actualFinal (stage :: tail)

/-- Repeatedly append using the actual current radius, until crossing or fuel
exhaustion. The stock budget pays every potential remaining deletion. -/
theorem fw_mixed_affine_actual_iterate_bounded (i : Fin 8) {n : ℕ}
    (fuel : ℕ) {initial S : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n + 8)) initial radius S last stages)
    (L M Mf eta : ℝ)
    (hlast : 0 < last) (heven : 2 ∣ last) (hL : 0 < L)
    (hS : S ⊆ (poolFinset n).filter (fun p => 43 < p))
    (heta : 0 < eta) (hMf : 0 < Mf) (hM : Mf ≤ M)
    (heps : 0 ≤ 1 / (2 * (1 + 1 / L)) - eta)
    (hshift : 0 < (last : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1
      (poolMaximum n) eta Mf)
    (hslope : fwAffineSlope eta 2 M 1 (poolMaximum n) / fwMixedWheelRho i ≤ 1)
    (hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * poolMaximum n ≤
      (1 / (2 * (1 + 1 / L)) - eta) * Mf ^ 2)
    (hbudget : M + ((2 * (6 * (n + 8)) * fuel : ℕ) : ℝ) ≤ (S.card : ℝ)) :
    ∃ (final : Finset ℕ) (actualFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial radius final actualFinal (stages ++ extra) ∧
      extra.length ≤ fuel ∧ final ⊆ S ∧
      final.card + 2 * (6 * (n + 8)) * extra.length = S.card ∧
      ((poolMaximum n : ℝ) / L ≤ actualFinal ∨ extra.length = fuel) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      last ≤ actualFinal ∧ 2 ∣ actualFinal ∧
      FWMixedAffineActualSchedule i n L M Mf eta last actualFinal extra := by
  induction fuel generalizing S last stages with
  | zero =>
    refine ⟨S, last, [], ?_, by simp, Finset.Subset.rfl, by simp, ?_, ?_, le_rfl, heven,
      FWMixedAffineActualSchedule.nil _⟩
    · simpa using trace
    · right; simp
    · simp [NarrowedStages]
  | succ fuel ih =>
    by_cases hdone : (poolMaximum n : ℝ) / L ≤ last
    · refine ⟨S, last, [], ?_, by simp, Finset.Subset.rfl, by simp, ?_, ?_, le_rfl, heven,
        FWMixedAffineActualSchedule.nil _⟩
      · simpa using trace
      · exact Or.inl hdone
      · simp [NarrowedStages]
    · have hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / L := lt_of_not_ge hdone
      have hstock : M ≤ (S.card : ℝ) := by
        have hp : (0 : ℝ) ≤ ((2 * (6 * (n + 8)) * (fuel + 1) : ℕ) : ℝ) := by positivity
        linarith
      obtain ⟨hD, hDR, gap, chosen, hgap, hdiv, hmin, hgain, hmax, hcard,
        hpairs, hmatch, hfoot, hsize, hdeplete, hmid, hradius, htrace⟩ :=
        fw_mixed_affine_append_stage i trace L M Mf eta hlast heven le_rfl hL
          (le_of_lt hnotdone) hS heta hMf hM hstock heps hshift hslope hquota
      let D := fwAffineThreshold 2 (fwMixedWheelRho i) eta M last 1 (poolMaximum n)
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
      have hbudget' := (fw_affine_stock_budget_succ hbudget hdeplete).2
      obtain ⟨final, actualFinal, extra, hfinal, hlen, hfinalSub, hfinalCard,
        hstop, hnarrow, hgrows, hefinal, hsched⟩ :=
        ih htrace hlast' heven' hS' hshift' hbudget'
      refine ⟨final, actualFinal, stage :: extra, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hefinal, ?_⟩
      · simpa [stage, List.append_assoc] using hfinal
      · simpa using Nat.succ_le_succ hlen
      · exact hfinalSub.trans Finset.sdiff_subset
      · change final.card + (2 * (6 * (n + 8))) * (extra.length + 1) = S.card
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · rcases hstop with hs | hs
        · exact Or.inl hs
        · right; simpa using congrArg Nat.succ hs
      · intro s hs p hp q hq
        rcases List.mem_cons.mp hs with rfl | hs
        · simpa [stage] using hmid p hp q hq
        · exact hnarrow s hs p hp q hq
      · omega
      · exact FWMixedAffineActualSchedule.cons last actualFinal stage extra hnotdone hshift
          rfl hgap hdiv hmin hgain hmax hsched

end
end Sude
