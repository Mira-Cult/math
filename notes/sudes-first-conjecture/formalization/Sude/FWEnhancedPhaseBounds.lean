import Sude.FWFullStockNumericLower
import Sude.FWFullStockLowerIteration
import Sude.FWIndexedAffineOrigins
import Sude.FWEnhancedNumericCertificate
import Sude.FWFirstWindowRadius105
import Sude.FWMixedScheduleSurplus

/-! Lower-radius propagation through eight supplied full-stock phases. The
finite recurrence equalities are proved in the separate numeric certificate;
this file does not assert phase existence, crossing, BT selection or physical
placement. -/
namespace Sude
noncomputable section

/-- Natural lower increment at one global index for a fixed source wheel. -/
def fwEnhancedPhaseIncrement (i : Fin 8) (j R : ℕ) : ℕ :=
  2 * fwEnhancedLowerCount i j R

/-- A supplied full-stock phase dominates its stage-indexed lower recurrence. -/
theorem fw_enhanced_phase_schedule_lower {i : Fin 8} {n j start finish : ℕ}
    {stages : List BTSelectedStage}
    (sched : FWFullStockSchedule i n j start finish stages) (r : ℕ) (hr : r ≤ start) :
    fwFullStockLowerIter (fwEnhancedPhaseIncrement i) stages.length j r ≤ finish := by
  apply fw_full_stock_schedule_lower_iter (fwEnhancedPhaseIncrement i) i n _ _ sched r hr
  · intro k a b hab
    exact Nat.mul_le_mul_left 2 (fw_enhanced_lower_count_mono i k hab)
  · intro k R gap hk hgap
    exact fw_enhanced_lower_increment_le_gap i (by omega) hgap

/-- Given the eight linked supplied schedules, their actual phase endpoints
dominate the certified recurrence bounds. No schedule existence or target
crossing is asserted. -/
theorem fw_enhanced_eight_supplied_phase_bounds {n : ℕ}
    {r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℕ}
    {s0 s1 s2 s3 s4 s5 s6 s7 : List BTSelectedStage}
    (hstart : 11648 ≤ r0)
    (h0 : FWFullStockSchedule 0 n 118 r0 r1 s0) (l0 : s0.length = 6)
    (h1 : FWFullStockSchedule 1 n 124 r1 r2 s1) (l1 : s1.length = 11)
    (h2 : FWFullStockSchedule 2 n 135 r2 r3 s2) (l2 : s2.length = 12)
    (h3 : FWFullStockSchedule 3 n 147 r3 r4 s3) (l3 : s3.length = 9)
    (h4 : FWFullStockSchedule 4 n 156 r4 r5 s4) (l4 : s4.length = 10)
    (h5 : FWFullStockSchedule 5 n 166 r5 r6 s5) (l5 : s5.length = 10)
    (h6 : FWFullStockSchedule 6 n 176 r6 r7 s6) (l6 : s6.length = 8)
    (h7 : FWFullStockSchedule 7 n 184 r7 r8 s7) (l7 : s7.length = 44)
 :
    18262 ≤ r1 ∧ 43062 ≤ r2 ∧ 114816 ≤ r3 ∧ 245862 ≤ r4 ∧
      586810 ≤ r5 ∧ 1430864 ≤ r6 ∧ 2960558 ≤ r7 ∧ 174846346 ≤ r8 := by
  have c0 : fwFullStockLowerIter (fwEnhancedPhaseIncrement 0) 6 118 11648 = 18262 := fw_enhanced_phase0_boundary
  have c1 : fwFullStockLowerIter (fwEnhancedPhaseIncrement 1) 11 124 18262 = 43062 := fw_enhanced_phase1_boundary
  have c2 : fwFullStockLowerIter (fwEnhancedPhaseIncrement 2) 12 135 43062 = 114816 := fw_enhanced_phase2_boundary
  have c3 : fwFullStockLowerIter (fwEnhancedPhaseIncrement 3) 9 147 114816 = 245862 := fw_enhanced_phase3_boundary
  have c4 : fwFullStockLowerIter (fwEnhancedPhaseIncrement 4) 10 156 245862 = 586810 := fw_enhanced_phase4_boundary
  have c5 : fwFullStockLowerIter (fwEnhancedPhaseIncrement 5) 10 166 586810 = 1430864 := fw_enhanced_phase5_boundary
  have c6 : fwFullStockLowerIter (fwEnhancedPhaseIncrement 6) 8 176 1430864 = 2960558 := fw_enhanced_phase6_boundary
  have c7 : fwFullStockLowerIter (fwEnhancedPhaseIncrement 7) 44 184 2960558 = 174846346 := fw_enhanced_phase7_boundary
  have b1 := fw_enhanced_phase_schedule_lower h0 11648 hstart
  rw [l0, c0] at b1
  have b2 := fw_enhanced_phase_schedule_lower h1 18262 b1
  rw [l1, c1] at b2
  have b3 := fw_enhanced_phase_schedule_lower h2 43062 b2
  rw [l2, c2] at b3
  have b4 := fw_enhanced_phase_schedule_lower h3 114816 b3
  rw [l3, c3] at b4
  have b5 := fw_enhanced_phase_schedule_lower h4 245862 b4
  rw [l4, c4] at b5
  have b6 := fw_enhanced_phase_schedule_lower h5 586810 b5
  rw [l5, c5] at b6
  have b7 := fw_enhanced_phase_schedule_lower h6 1430864 b6
  rw [l6, c6] at b7
  have b8 := fw_enhanced_phase_schedule_lower h7 2960558 b7
  rw [l7, c7] at b8
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩

/-- The phase bounds are sufficient for all eight indexed origin thresholds. -/
theorem fw_enhanced_phase_bounds_pay_origins {r0 r1 r2 r3 r4 r5 r6 r7 : ℕ}
    (h0 : 11648 ≤ r0) (h1 : 18262 ≤ r1) (h2 : 43062 ≤ r2)
    (h3 : 114816 ≤ r3) (h4 : 245862 ≤ r4) (h5 : 586810 ≤ r5)
    (h6 : 1430864 ≤ r6) (h7 : 2960558 ≤ r7) :
    fwAffineOriginUpper 0 ≤ r0 ∧ fwAffineOriginUpper 1 ≤ r1 ∧
      fwAffineOriginUpper 2 ≤ r2 ∧ fwAffineOriginUpper 3 ≤ r3 ∧
      fwAffineOriginUpper 4 ≤ r4 ∧ fwAffineOriginUpper 5 ≤ r5 ∧
      fwAffineOriginUpper 6 ≤ r6 ∧ fwAffineOriginUpper 7 ≤ r7 := by
  change 1108 ≤ r0 ∧ 2196 ≤ r1 ∧ 4380 ≤ r2 ∧ 8747 ≤ r3 ∧
    17479 ≤ r4 ∧ 34942 ≤ r5 ∧ 69868 ≤ r6 ∧ 139718 ≤ r7
  omega

/-- A supplied completed first-window schedule has actual radius at least its
certified 105-wheel lower bound. No existence or crossing is asserted. -/
theorem fw_enhanced_completed_window_actual_lower
    {X : ℝ} {R0 r0 : ℕ} {window : List BTSelectedStage}
    (hwindow : FWFirstWindowCertifiedSchedule X 0 32 32 R0 r0 window)
    (hwindowlen : window.length = 118) : 11648 ≤ r0 := by
  have hcert := fw_certified_118_radius_at_least_11648 hwindow hwindowlen
  have hsurplus := fw_first_window_schedule_surplus hwindow
  omega

/-- A completed first-window schedule followed by eight supplied linked
full-stock schedules pays all the stated actual-radius bounds. -/
theorem fw_enhanced_window_and_eight_supplied_phase_bounds {n : ℕ}
    {R0 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℕ}
    {window s0 s1 s2 s3 s4 s5 s6 s7 : List BTSelectedStage}
    (hwindow : FWFirstWindowCertifiedSchedule (poolMaximum n) 0 32 32 R0 r0 window)
    (hwindowlen : window.length = 118)
    (h0 : FWFullStockSchedule 0 n 118 r0 r1 s0) (l0 : s0.length = 6)
    (h1 : FWFullStockSchedule 1 n 124 r1 r2 s1) (l1 : s1.length = 11)
    (h2 : FWFullStockSchedule 2 n 135 r2 r3 s2) (l2 : s2.length = 12)
    (h3 : FWFullStockSchedule 3 n 147 r3 r4 s3) (l3 : s3.length = 9)
    (h4 : FWFullStockSchedule 4 n 156 r4 r5 s4) (l4 : s4.length = 10)
    (h5 : FWFullStockSchedule 5 n 166 r5 r6 s5) (l5 : s5.length = 10)
    (h6 : FWFullStockSchedule 6 n 176 r6 r7 s6) (l6 : s6.length = 8)
    (h7 : FWFullStockSchedule 7 n 184 r7 r8 s7) (l7 : s7.length = 44) :
    11648 ≤ r0 ∧ 18262 ≤ r1 ∧ 43062 ≤ r2 ∧ 114816 ≤ r3 ∧
      245862 ≤ r4 ∧ 586810 ≤ r5 ∧ 1430864 ≤ r6 ∧
      2960558 ≤ r7 ∧ 174846346 ≤ r8 := by
  have hstart := fw_enhanced_completed_window_actual_lower hwindow hwindowlen
  exact ⟨hstart, fw_enhanced_eight_supplied_phase_bounds hstart h0 l0 h1 l1 h2 l2
    h3 l3 h4 l4 h5 l5 h6 l6 h7 l7⟩

/-- The terminal bound pays the previously established fixed-mass BT entry
radius. It does not itself supply the BT stock or analytic conditions. -/
theorem fw_enhanced_terminal_pays_bt_radius {r8 : ℕ} (h : 174846346 ≤ r8) :
    171331843 ≤ r8 := by omega

/-- The phase-start radii in source-wheel order. -/
def fwEnhancedPhaseStarts (r0 r1 r2 r3 r4 r5 r6 r7 : ℕ) : Fin 8 → ℕ :=
  ![r0, r1, r2, r3, r4, r5, r6, r7]

/-- The derived numerical bounds pay each indexed strict source-origin gate.
The positivity of X is explicit, and the phase radii remain supplied. -/
theorem fw_enhanced_phase_bounds_pay_shifts {X : ℝ}
    {r0 r1 r2 r3 r4 r5 r6 r7 : ℕ} (hX : 0 < X)
    (h0 : 11648 ≤ r0) (h1 : 18262 ≤ r1) (h2 : 43062 ≤ r2)
    (h3 : 114816 ≤ r3) (h4 : 245862 ≤ r4) (h5 : 586810 ≤ r5)
    (h6 : 1430864 ≤ r6) (h7 : 2960558 ≤ r7) :
    ∀ i : Fin 8, 0 < ((fwEnhancedPhaseStarts r0 r1 r2 r3 r4 r5 r6 r7 i : ℕ) : ℝ) -
      fwAffineOrigin (fwMixedWheelError i) 1 X (3981035 / 10000000)
        ((3257 / 100000 : ℝ) * X) := by
  have horig := fw_enhanced_phase_bounds_pay_origins h0 h1 h2 h3 h4 h5 h6 h7
  intro i
  have hbound : fwAffineOriginUpper i ≤ fwEnhancedPhaseStarts r0 r1 r2 r3 r4 r5 r6 r7 i := by
    fin_cases i
    · exact horig.1
    · exact horig.2.1
    · exact horig.2.2.1
    · exact horig.2.2.2.1
    · exact horig.2.2.2.2.1
    · exact horig.2.2.2.2.2.1
    · exact horig.2.2.2.2.2.2.1
    · exact horig.2.2.2.2.2.2.2
  exact fw_indexed_affine_shift_of_radius i hX (by norm_num) hbound

end
end Sude
