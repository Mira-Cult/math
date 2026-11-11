import Sude.FWFirstWindowCertifiedRadius
import Sude.FWFullStockIteration

/-! Upper bounds for the actual radius recorded by the two first-band
    schedules. These lemmas do not select a crossing witness. -/
namespace Sude
noncomputable section

theorem fw_first_window_schedule_radius_upper {X : ℝ}
    {j R start Rfinal final : ℕ} {stages : List BTSelectedStage}
    (h : FWFirstWindowCertifiedSchedule X j R start Rfinal final stages) :
    (final : ℝ) ≤ max (start : ℝ) (2 * (X / 23)) := by
  induction h with
  | nil => exact le_max_left _ _
  | cons j R actual Rfinal final stage tail hcap hbefore hbelow hfloor hminimum
      hpositive heven hlower hupper hrest ih =>
    have hgap : (stage.gap : ℝ) ≤ actual := by
      exact_mod_cast hupper.trans hbelow
    have hnext : ((actual + stage.gap : ℕ) : ℝ) ≤ 2 * (X / 23) := by
      push_cast
      linarith
    exact ih.trans (max_le (hnext.trans (le_max_right _ _)) (le_max_right _ _))

theorem fw_full_stock_schedule_radius_upper {i : Fin 8} {n j start final : ℕ}
    {stages : List BTSelectedStage} (h : FWFullStockSchedule i n j start final stages) :
    (final : ℝ) ≤ max (start : ℝ) (2 * ((poolMaximum n : ℝ) / 23)) := by
  induction h with
  | nil => exact le_max_left _ _
  | cons j actual final stage tail hcap hbefore hshift hminimum hpositive heven
      henhanced hplus hupper hrest ih =>
    have hgap : (stage.gap : ℝ) ≤ actual := by exact_mod_cast hupper
    have hnext : ((actual + stage.gap : ℕ) : ℝ) ≤ 2 * ((poolMaximum n : ℝ) / 23) := by
      push_cast
      linarith
    exact ih.trans (max_le (hnext.trans (le_max_right _ _)) (le_max_right _ _))

end
end Sude
