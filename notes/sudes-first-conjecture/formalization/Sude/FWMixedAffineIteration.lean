import Sude.FWMixedAffineCertifiedStep
import Sude.BTNarrowIteration

/-! Conditional bounded same-wheel continuation. The conservative stock
budget is explicit, and neither crossing nor a frozen mixed recipe is proved. -/
namespace Sude
noncomputable section

/-- One exact `2Q` depletion preserves the conservative remaining budget. -/
theorem fw_affine_stock_budget_succ {M : ℝ} {Q fuel : ℕ} {S S' : Finset ℕ}
    (hbudget : M + ((2 * Q * (fuel + 1) : ℕ) : ℝ) ≤ (S.card : ℝ))
    (hdeplete : S'.card + 2 * Q = S.card) :
    M ≤ (S.card : ℝ) ∧ M + ((2 * Q * fuel : ℕ) : ℝ) ≤ (S'.card : ℝ) := by
  have hd : (S'.card : ℝ) + ((2 * Q : ℕ) : ℝ) = (S.card : ℝ) := by exact_mod_cast hdeplete
  have hp : (0 : ℝ) ≤ ((2 * Q * (fuel + 1) : ℕ) : ℝ) := by positivity
  push_cast at *
  constructor <;> nlinarith

/-- A supplied trace can be extended on one fixed wheel until crossing or
fuel exhaustion, if enough stock is reserved for every remaining step. -/
theorem fw_mixed_affine_iterate_bounded (i : Fin 8) {n : ℕ}
    (fuel : ℕ) {initial S : Finset ℕ} {radius R last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n + 8)) initial radius S last stages)
    (L M Mf eta : ℝ)
    (hR : 0 < R) (heven : 2 ∣ R) (hbelow : R ≤ last) (hL : 0 < L)
    (hS : S ⊆ (poolFinset n).filter (fun p => 43 < p))
    (heta : 0 < eta) (hMf : 0 < Mf) (hM : Mf ≤ M)
    (heps : 0 ≤ 1 / (2 * (1 + 1 / L)) - eta)
    (hshift : 0 < (R : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1
      (poolMaximum n) eta Mf)
    (hslope : fwAffineSlope eta 2 M 1 (poolMaximum n) / fwMixedWheelRho i ≤ 1)
    (hquota : ((6 * (6 * (n + 8)) : ℕ) : ℝ) * poolMaximum n ≤
      (1 / (2 * (1 + 1 / L)) - eta) * Mf ^ 2)
    (hbudget : M + ((2 * (6 * (n + 8)) * fuel : ℕ) : ℝ) ≤ (S.card : ℝ)) :
    ∃ (final : Finset ℕ) (Rfinal actualFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial radius final actualFinal (stages ++ extra) ∧
      extra.length ≤ fuel ∧ final ⊆ S ∧
      final.card + 2 * (6 * (n + 8)) * extra.length = S.card ∧
      ((poolMaximum n : ℝ) / L ≤ actualFinal ∨ extra.length = fuel) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      R ≤ Rfinal ∧ 2 ∣ Rfinal ∧ Rfinal ≤ actualFinal ∧
      FWMixedAffineCertifiedSchedule i n L M Mf eta R last Rfinal actualFinal extra := by
  induction fuel generalizing S R last stages with
  | zero =>
    refine ⟨S, R, last, [], ?_, by simp, Finset.Subset.rfl, by simp, ?_, ?_, le_rfl, heven, hbelow,
      FWMixedAffineCertifiedSchedule.nil _ _⟩
    · simpa using trace
    · right; simp
    · simp [NarrowedStages]
  | succ fuel ih =>
    by_cases hdone : (poolMaximum n : ℝ) / L ≤ last
    · refine ⟨S, R, last, [], ?_, by simp, Finset.Subset.rfl, by simp, ?_, ?_, le_rfl, heven, hbelow,
        FWMixedAffineCertifiedSchedule.nil _ _⟩
      · simpa using trace
      · exact Or.inl hdone
      · simp [NarrowedStages]
    · have hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / L := lt_of_not_ge hdone
      have hbefore : (R : ℝ) ≤ (poolMaximum n : ℝ) / L := by
        have hb : (R : ℝ) ≤ last := by exact_mod_cast hbelow
        exact le_trans hb (le_of_lt hnotdone)
      have hstock : M ≤ (S.card : ℝ) := by
        have hp : (0 : ℝ) ≤ ((2 * (6 * (n + 8)) * (fuel + 1) : ℕ) : ℝ) := by positivity
        linarith
      obtain ⟨hD, hDR, gap, chosen, hgap, hdiv, hmin, hgain, hmax, hcard,
        hpairs, hmatch, hfoot, hsize, hdeplete, hmid, hradius, htrace⟩ :=
        fw_mixed_affine_append_stage i trace L M Mf eta hR heven hbelow hL hbefore hS
          heta hMf hM hstock heps hshift hslope hquota
      let D := fwAffineThreshold 2 (fwMixedWheelRho i) eta M R 1 (poolMaximum n) (fwMixedWheelError i)
      let k := fwMixedAffineEvenIncrement i n R M eta
      let stage : BTSelectedStage := ⟨gap, chosen, D⟩
      have hk : 0 < k ∧ 2 ∣ k ∧ k ≤ gap := by
        have hkraw := fw_even_ceiling_threshold hD hdiv hmin
        exact ⟨by simpa [k, D, fwMixedAffineEvenIncrement] using hkraw.1,
          by simp [k, fwMixedAffineEvenIncrement],
          by simpa [k, D, fwMixedAffineEvenIncrement] using hkraw.2.2.2⟩
      have hR' : 0 < R + k := by omega
      have heven' : 2 ∣ R + k := dvd_add heven hk.2.1
      have hbelow' : R + k ≤ last + gap := Nat.add_le_add hbelow hk.2.2
      have hS' : S \ pairFootprint chosen gap ⊆ (poolFinset n).filter (fun p => 43 < p) :=
        Finset.sdiff_subset.trans hS
      have hshift' : 0 < ((R + k : ℕ) : ℝ) -
          fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n) eta Mf := by
        push_cast
        have hk0 : (0 : ℝ) ≤ k := by positivity
        linarith
      have hbudget' := (fw_affine_stock_budget_succ hbudget hdeplete).2
      obtain ⟨final, Rfinal, actualFinal, extra, hfinal, hlen, hfinalSub, hfinalCard,
        hstop, hnarrow, hRgrows, hefinal, hlfinal, hsched⟩ :=
        ih htrace hR' heven' hbelow' hS' hshift' hbudget'
      refine ⟨final, Rfinal, actualFinal, stage :: extra, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hefinal,
        hlfinal, ?_⟩
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
      · exact FWMixedAffineCertifiedSchedule.cons R last Rfinal actualFinal stage extra hnotdone
          hbelow hshift rfl hgap hdiv hmin hmax hsched

end
end Sude
