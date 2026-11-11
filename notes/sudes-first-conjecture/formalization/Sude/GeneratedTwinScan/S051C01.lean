import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107085869 107118637 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 107085869 107118637).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107085869 107118637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107118637 107151405 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 107118637 107151405).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107118637 107151405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107151405 107184173 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 107151405 107184173).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107151405 107184173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107184173 107216941 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 107184173 107216941).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107184173 107216941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 107085869 107151405).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 107085869 ≤ 107118637)
    (by decide : 107118637 ≤ 107151405) block0 block1

theorem join_0_1 : (twinPrimeSegment 107151405 107216941).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 107151405 ≤ 107184173)
    (by decide : 107184173 ≤ 107216941) block2 block3

theorem join_1_0 : (twinPrimeSegment 107085869 107216941).card = 509 := by
  simpa using combineTwinPrimeSegments (by decide : 107085869 ≤ 107151405)
    (by decide : 107151405 ≤ 107216941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 107085869 107216941).card = 509 := join_1_0

end S051C01
end Sude.GeneratedTwinScan
