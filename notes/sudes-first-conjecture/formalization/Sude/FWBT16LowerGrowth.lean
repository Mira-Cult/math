import Sude.FWBT16EntryGate
import Sude.FWWheelFirstBandEnvelopes
import Sude.BTGrowingWidths

/-! A conservative fixed-mass BT growth recurrence. The calculations here
are conditional on supplied width bounds; no BT stage or trace is constructed. -/
namespace Sude
noncomputable section

/-- The source's fixed-mass width for g=2 and lambda=16. -/
def fwBT16FixedWidth (R : ℕ) : ℝ :=
  8 * ((3981035 / 10000000 : ℝ) * (3257 / 100000 : ℝ) * R - 1 / 2)

/-- An integer lower bound on the fixed-mass source width. -/
def fwBT16LowerIncrement (R : ℕ) : ℕ :=
  (2593246199 * R - 100000000000) / 25000000000

def fwBT16LowerIter : ℕ → ℕ → ℕ
  | 0, R => R
  | k + 1, R => fwBT16LowerIter k (R + fwBT16LowerIncrement R)

theorem fw_bt16_increment_mono : Monotone fwBT16LowerIncrement := by
  intro a b hab
  unfold fwBT16LowerIncrement
  apply Nat.div_le_div_right
  exact Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hab) _

theorem fw_bt16_increment_le_gap {R gap : ℕ} (hR : 39 ≤ R)
    (hgap : fwBT16FixedWidth R ≤ (gap : ℝ)) : fwBT16LowerIncrement R ≤ gap := by
  have hRnum : 100000000000 ≤ 2593246199 * R := by omega
  have hsub : (((2593246199 * R - 100000000000 : ℕ) : ℝ)) =
      (2593246199 : ℝ) * R - 100000000000 := by
    rw [Nat.cast_sub hRnum]
    push_cast
    ring
  have hdiv : ((fwBT16LowerIncrement R : ℕ) : ℝ) ≤
      ((2593246199 * R - 100000000000 : ℕ) : ℝ) / 25000000000 := by
    unfold fwBT16LowerIncrement
    exact_mod_cast (Nat.cast_div_le (α := ℝ)
      (m := 2593246199 * R - 100000000000) (n := 25000000000))
  rw [hsub] at hdiv
  have hbound : ((fwBT16LowerIncrement R : ℕ) : ℝ) ≤ (gap : ℝ) := by
    unfold fwBT16FixedWidth at hgap
    nlinarith
  exact_mod_cast hbound

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact value of the weaker ten-step natural recurrence. -/
theorem fw_bt16_lower_iter_10 : fwBT16LowerIter 10 174846346 = 469120449 := by
  decide +kernel

/-- First-band sharp RS bound places the target below the finite endpoint. -/
theorem fw_bt16_lower_iter_above_target (upper : RSIndexUpperSharp) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) :
    (poolMaximum n : ℝ) / 23 < fwBT16LowerIter 10 174846346 := by
  have hx := fw_first_band_upper_index_ratio upper hnlo hnhi
  have hn : (n : ℝ) ≤ 21248 := by exact_mod_cast hnhi
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hs : (n : ℝ)^2 ≤ (21248 : ℝ)^2 := by nlinarith
  rw [fw_bt16_lower_iter_10]
  norm_num at *
  nlinarith

end
end Sude
