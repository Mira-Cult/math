import Sude.FWFullStockNumericLower
import Sude.FWFullStockLowerIteration

/-! Finite arithmetic source for the conservative full-stock affine lower
recurrence. Each declaration is an exact kernel decision; this file by itself
does not establish existence of a schedule, BT entry or crossing. -/
namespace Sude

/-- Lower integer recurrence for a fixed wheel and a specified global index. -/
def fwEnhancedPhaseRun (i : Fin 8) (j fuel R : ℕ) : ℕ :=
  fwFullStockLowerIter (fun k r => 2 * fwEnhancedLowerCount i k r) fuel j R

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Six first-wheel stages from the checked initial radius. -/
theorem fw_enhanced_phase0_boundary : fwEnhancedPhaseRun 0 118 6 11648 = 18262 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_enhanced_phase1_boundary : fwEnhancedPhaseRun 1 124 11 18262 = 43062 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_enhanced_phase2_boundary : fwEnhancedPhaseRun 2 135 12 43062 = 114816 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_enhanced_phase3_boundary : fwEnhancedPhaseRun 3 147 9 114816 = 245862 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_enhanced_phase4_boundary : fwEnhancedPhaseRun 4 156 10 245862 = 586810 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_enhanced_phase5_boundary : fwEnhancedPhaseRun 5 166 10 586810 = 1430864 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_enhanced_phase6_boundary : fwEnhancedPhaseRun 6 176 8 1430864 = 2960558 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_enhanced_phase7_boundary : fwEnhancedPhaseRun 7 184 44 2960558 = 174846346 := by decide +kernel

/-- All eight conservative affine phases in the source's wheel order. -/
def fwEnhancedAllPhases (R : ℕ) : ℕ :=
  let r0 := fwEnhancedPhaseRun 0 118 6 R
  let r1 := fwEnhancedPhaseRun 1 124 11 r0
  let r2 := fwEnhancedPhaseRun 2 135 12 r1
  let r3 := fwEnhancedPhaseRun 3 147 9 r2
  let r4 := fwEnhancedPhaseRun 4 156 10 r3
  let r5 := fwEnhancedPhaseRun 5 166 10 r4
  let r6 := fwEnhancedPhaseRun 6 176 8 r5
  fwEnhancedPhaseRun 7 184 44 r6

/-- Finite recurrence endpoint; no trace or crossing is asserted. -/
theorem fw_enhanced_110_stage_endpoint : fwEnhancedAllPhases 11648 = 174846346 := by
  simp only [fwEnhancedAllPhases, fw_enhanced_phase0_boundary, fw_enhanced_phase1_boundary,
    fw_enhanced_phase2_boundary, fw_enhanced_phase3_boundary, fw_enhanced_phase4_boundary,
    fw_enhanced_phase5_boundary, fw_enhanced_phase6_boundary, fw_enhanced_phase7_boundary]

/-- The finite recurrence clears the previously proved conditional BT radius
threshold. This is only arithmetic until linked to supplied stage schedules. -/
theorem fw_enhanced_110_stage_bt_radius : 171331843 ≤ fwEnhancedAllPhases 11648 := by
  rw [fw_enhanced_110_stage_endpoint]
  decide

end Sude
