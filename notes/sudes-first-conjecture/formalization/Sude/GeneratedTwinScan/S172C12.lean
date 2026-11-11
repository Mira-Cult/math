import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19034)) 362283053 362315821 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 362283053 362315821).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19034 362283053 362315821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19035)) 362315821 362348589 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 362315821 362348589).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19035 362315821 362348589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19036)) 362348589 362381357 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 362348589 362381357).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19036 362348589 362381357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19037)) 362381357 362414125 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 362381357 362414125).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19037 362381357 362414125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 362283053 362348589).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 362283053 ≤ 362315821)
    (by decide : 362315821 ≤ 362348589) block0 block1

theorem join_0_1 : (twinPrimeSegment 362348589 362414125).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 362348589 ≤ 362381357)
    (by decide : 362381357 ≤ 362414125) block2 block3

theorem join_1_0 : (twinPrimeSegment 362283053 362414125).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 362283053 ≤ 362348589)
    (by decide : 362348589 ≤ 362414125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 362283053 362414125).card = 447 := join_1_0

end S172C12
end Sude.GeneratedTwinScan
