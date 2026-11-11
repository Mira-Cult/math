import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118358061 118390829 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 118358061 118390829).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118358061 118390829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118390829 118423597 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 118390829 118423597).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118390829 118423597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118423597 118456365 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 118423597 118456365).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118423597 118456365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118456365 118489133 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 118456365 118489133).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118456365 118489133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 118358061 118423597).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 118358061 ≤ 118390829)
    (by decide : 118390829 ≤ 118423597) block0 block1

theorem join_0_1 : (twinPrimeSegment 118423597 118489133).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 118423597 ≤ 118456365)
    (by decide : 118456365 ≤ 118489133) block2 block3

theorem join_1_0 : (twinPrimeSegment 118358061 118489133).card = 500 := by
  simpa using combineTwinPrimeSegments (by decide : 118358061 ≤ 118423597)
    (by decide : 118423597 ≤ 118489133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 118358061 118489133).card = 500 := join_1_0

end S056C07
end Sude.GeneratedTwinScan
