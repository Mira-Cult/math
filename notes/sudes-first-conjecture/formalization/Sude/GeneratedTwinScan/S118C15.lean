import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15794)) 249430061 249462829 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 249430061 249462829).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15794 249430061 249462829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15795)) 249462829 249495597 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 249462829 249495597).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15795 249462829 249495597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15796)) 249495597 249528365 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 249495597 249528365).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15796 249495597 249528365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15797)) 249528365 249561133 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 249528365 249561133).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15797 249528365 249561133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 249430061 249495597).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 249430061 ≤ 249462829)
    (by decide : 249462829 ≤ 249495597) block0 block1

theorem join_0_1 : (twinPrimeSegment 249495597 249561133).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 249495597 ≤ 249528365)
    (by decide : 249528365 ≤ 249561133) block2 block3

theorem join_1_0 : (twinPrimeSegment 249430061 249561133).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 249430061 ≤ 249495597)
    (by decide : 249495597 ≤ 249561133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 249430061 249561133).card = 466 := join_1_0

end S118C15
end Sude.GeneratedTwinScan
