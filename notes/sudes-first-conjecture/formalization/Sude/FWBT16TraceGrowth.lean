import Sude.FWBT16LowerGrowth
import Sude.BTIndexedTraceLower

/-! Conditional ten-stage growth from explicitly supplied BT widths.
No BT stages, trace, or source analytic inputs are constructed here. -/
namespace Sude
noncomputable section

def fwBT16LowerTable (i : ℕ) : ℕ :=
  ([174846346, 192983126, 213001232, 235095813, 259482261, 286398312,
    316106361, 348896021, 385086948, 425031954, 469120449] : List ℕ).getD i 0

theorem fw_bt16_table_floor : ∀ i ≤ 10, 39 ≤ fwBT16LowerTable i := by
  intro i hi
  interval_cases i <;> norm_num [fwBT16LowerTable]

theorem fw_bt16_table_step : ∀ i < 10,
    fwBT16LowerTable (i + 1) ≤
      fwBT16LowerTable i + fwBT16LowerIncrement (fwBT16LowerTable i) := by
  intro i hi
  interval_cases i <;> norm_num [fwBT16LowerTable, fwBT16LowerIncrement]

theorem fw_bt16_ten_width_stages_cross
    (upper : RSIndexUpperSharp) {n g Q : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    {initial final : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (widths : BTWidthTrace (fun _ r => fwBT16FixedWidth r) 0 radius stages)
    (hstart : 174846346 ≤ radius) (hlen : stages.length = 10) :
    (poolMaximum n : ℝ) / 23 < last := by
  have hstart' : fwBT16LowerTable 0 ≤ radius := by
    simpa [fwBT16LowerTable] using hstart
  have hh := fw_bt_bounded_indexed_width_trace_lower
    fwBT16LowerTable fwBT16LowerIncrement (fun _ r => fwBT16FixedWidth r)
    fw_bt16_table_floor fw_bt16_table_step fw_bt16_increment_mono
    (fun _ _ _ hR hgap => fw_bt16_increment_le_gap hR hgap)
    widths (fun stage hs => (trace.stage_properties stage hs).2.2.1)
    0 (by simp [hlen]) hstart'
  have hend : 469120449 ≤ last := by
    have hlast := trace.final_accounting.2.2
    rw [hlast]
    simpa [hlen, fwBT16LowerTable] using hh
  have htarget := fw_bt16_lower_iter_above_target upper hnlo hnhi
  rw [fw_bt16_lower_iter_10] at htarget
  exact htarget.trans_le (by exact_mod_cast hend)

end
end Sude
