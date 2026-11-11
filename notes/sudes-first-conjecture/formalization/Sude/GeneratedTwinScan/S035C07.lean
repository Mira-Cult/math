import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74317869 74350637 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 74317869 74350637).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74317869 74350637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74350637 74383405 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 74350637 74383405).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74350637 74383405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74383405 74416173 = 151 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 74383405 74416173).card = 151 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74383405 74416173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74416173 74448941 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 74416173 74448941).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74416173 74448941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 74317869 74383405).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 74317869 ≤ 74350637)
    (by decide : 74350637 ≤ 74383405) block0 block1

theorem join_0_1 : (twinPrimeSegment 74383405 74448941).card = 290 := by
  simpa using combineTwinPrimeSegments (by decide : 74383405 ≤ 74416173)
    (by decide : 74416173 ≤ 74448941) block2 block3

theorem join_1_0 : (twinPrimeSegment 74317869 74448941).card = 558 := by
  simpa using combineTwinPrimeSegments (by decide : 74317869 ≤ 74383405)
    (by decide : 74383405 ≤ 74448941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 74317869 74448941).card = 558 := join_1_0

end S035C07
end Sude.GeneratedTwinScan
