import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121241645 121274413 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 121241645 121274413).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121241645 121274413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121274413 121307181 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 121274413 121307181).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121274413 121307181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121307181 121339949 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 121307181 121339949).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121307181 121339949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121339949 121372717 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 121339949 121372717).card = 107 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121339949 121372717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 121241645 121307181).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 121241645 ≤ 121274413)
    (by decide : 121274413 ≤ 121307181) block0 block1

theorem join_0_1 : (twinPrimeSegment 121307181 121372717).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 121307181 ≤ 121339949)
    (by decide : 121339949 ≤ 121372717) block2 block3

theorem join_1_0 : (twinPrimeSegment 121241645 121372717).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 121241645 ≤ 121307181)
    (by decide : 121307181 ≤ 121372717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 121241645 121372717).card = 496 := join_1_0

end S057C13
end Sude.GeneratedTwinScan
