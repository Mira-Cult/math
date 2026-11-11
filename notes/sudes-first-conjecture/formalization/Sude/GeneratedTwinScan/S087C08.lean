import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13547)) 183500845 183533613 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 183500845 183533613).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13547 183500845 183533613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13548)) 183533613 183566381 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 183533613 183566381).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13548 183533613 183566381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13549)) 183566381 183599149 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 183566381 183599149).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13549 183566381 183599149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13551)) 183599149 183631917 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 183599149 183631917).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13551 183599149 183631917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 183500845 183566381).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 183500845 ≤ 183533613)
    (by decide : 183533613 ≤ 183566381) block0 block1

theorem join_0_1 : (twinPrimeSegment 183566381 183631917).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 183566381 ≤ 183599149)
    (by decide : 183599149 ≤ 183631917) block2 block3

theorem join_1_0 : (twinPrimeSegment 183500845 183631917).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 183500845 ≤ 183566381)
    (by decide : 183566381 ≤ 183631917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 183500845 183631917).card = 478 := join_1_0

end S087C08
end Sude.GeneratedTwinScan
