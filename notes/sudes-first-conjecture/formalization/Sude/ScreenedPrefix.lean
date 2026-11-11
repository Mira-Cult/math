import Sude.ScreenedPool

/-! Actual screened-pool `g=2` prefix under explicit scalar arithmetic. -/
namespace Sude
noncomputable section

/-- Scalar data for one screened-pool prefix. These fields are internal
numerical obligations, not trusted analytic imports or a controller claim. -/
structure ScreenedPrefixNumerics (n z Q apSteps btSteps radius : ℕ) (reserved : Finset ℕ) where
  L : ℝ
  η : ℝ
  ell : ℝ
  Ma : ℝ
  Mb : ℝ
  Mf : ℝ
  target : ℝ
  L_pos : 0 < L
  eta_pos : 0 < η
  ell_pos : 0 < ell
  Mf_pos : 0 < Mf
  Ma_nonneg : 0 ≤ Ma
  Mb_nonneg : 0 ≤ Mb
  target_pos : 0 < target
  Ma_le_stock : Ma ≤ ((n * n : ℕ) : ℝ) - 13 - reserved.card
  epsilon_nonneg : 0 ≤ 1 / (2 * (1 + 1 / L)) - η
  stage_stock : 2 * Q * (apSteps + btSteps) + reserved.card + 13 < n * n
  floor_ap : Mf ≤ Ma - 2 * Q * (apSteps : ℝ)
  floor_bt : Mf ≤ Mb - 2 * Q * (btSteps : ℝ)
  reserve_bt : Mb + 2 * Q * (apSteps : ℝ) ≤ Ma
  pair_budget : 2 * ((z * Q : ℕ) : ℝ) * (poolMaximum n : ℝ) ≤
    (1 / (2 * (1 + 1 / L)) - η) * Mf ^ 2 * 2
  shifted_start : 0 < (radius : ℝ) - (poolMaximum n : ℝ) / (2 * η * Mf)
  final_cap : target ≤ (poolMaximum n : ℝ) / L - (poolMaximum n : ℝ) / (2 * η * Mf)
  ap_budget :
    Real.log (min ((poolMaximum n : ℝ) * Real.exp ell /
      ((ell * (Nat.totient 2 : ℝ) / (2 * 2)) * η * Mf)) target /
        ((radius : ℝ) - (poolMaximum n : ℝ) / (2 * η * Mf))) ≤
      (η * 2 / (poolMaximum n : ℝ)) *
        ((apSteps : ℝ) * Ma - Q * (apSteps : ℝ) * ((apSteps : ℝ) - 1)) /
          (1 + (η * 2 / (poolMaximum n : ℝ)) * Ma)
  bt_budget :
    Real.log (target / ((poolMaximum n : ℝ) * Real.exp ell /
      ((ell * (Nat.totient 2 : ℝ) / (2 * 2)) * η * Mf))) ≤
      ((ell * (Nat.totient 2 : ℝ) / (2 * 2)) * η * 2 / (poolMaximum n : ℝ)) *
        ((btSteps : ℝ) * Mb - Q * (btSteps : ℝ) * ((btSteps : ℝ) - 1)) /
          (1 + ((ell * (Nat.totient 2 : ℝ) / (2 * 2)) * η * 2 / (poolMaximum n : ℝ)) * Mb)

/-- Under the published MV premise and the displayed scalar obligations,
the actual screened prescribed pool yields a physical narrowed prefix. -/
theorem screened_pool_narrow_prefix (mv : MVBrunTitchmarsh)
    (n z Q apSteps btSteps radius : ℕ) (reserved : Finset ℕ)
    (hn : 13 ≤ n * n) (hz : 0 < z) (hradius : 0 < radius)
    (data : ScreenedPrefixNumerics n z Q apSteps btSteps radius reserved) :
    let S := (poolFinset n).filter (fun p => 43 < p) \ reserved
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 Q S radius final last stages ∧
      stages.length ≤ apSteps + btSteps ∧ final ⊆ S ∧
      final.card + 2 * Q * stages.length = S.card ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      NarrowedStages ((poolMaximum n : ℝ) / z) stages ∧
      data.target ≤ (last : ℝ) - (poolMaximum n : ℝ) / (2 * data.η * data.Mf) := by
  dsimp only
  let S := (poolFinset n).filter (fun p => 43 < p) \ reserved
  let X : ℝ := poolMaximum n
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hin := screened_pool_phase_inputs n z reserved hn hz
  have hstock := screened_pool_after_reservations n reserved hn
  have hMa : data.Ma ≤ S.card := data.Ma_le_stock.trans hin.1
  have hstages : 2 * Q * (apSteps + btSteps) < S.card := by
    have h1 : n * n ≤ S.card + reserved.card + 13 := hstock.1
    have h2 := data.stage_stock
    omega
  have hreduced : ∀ a ∈ ({1} : Finset ℕ), 0 < a ∧ Nat.Coprime 2 a := by
    intro a ha
    have ha' : a = 1 := by simpa using ha
    subst a
    norm_num
  have hclass : (({1} : Finset ℕ).card : ℝ) ≤ 1 := by norm_num
  have hinterval : ∀ p ∈ S, (1 : ℝ) ≤ p ∧ (p : ℝ) ≤ 1 + 1 * X := by
    intro p hp
    simpa [X] using hin.2.2.2.1 p hp
  have h := ap_then_bt_narrow_with_minimum_budget mv S {1} 1 1 X 1 data.L data.η data.ell
    data.Ma data.Mb data.Mf data.target radius 2 Q apSteps btSteps z 1 (X / z)
    hz hin.2.2.2.2.2.1 hin.2.2.2.2.2.2 hin.2.2.1 hinterval hin.2.2.2.2.1 hreduced
    (by norm_num) hX (by norm_num) data.L_pos (by norm_num) data.eta_pos data.ell_pos
    data.Mf_pos data.Ma_nonneg data.Mb_nonneg hMa data.target_pos data.epsilon_nonneg
    hradius hclass hstages data.floor_ap data.floor_bt data.reserve_bt
    (by simpa [X] using data.pair_budget) (by simpa [X] using data.shifted_start)
    (by simpa [X] using data.final_cap) (by simpa [X] using data.ap_budget)
    (by simpa [X] using data.bt_budget)
  simpa [S, X] using h

end
end Sude
