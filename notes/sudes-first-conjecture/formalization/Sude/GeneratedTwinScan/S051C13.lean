import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108658733 108691501 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 108658733 108691501).card = 103 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108658733 108691501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108691501 108724269 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 108691501 108724269).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108691501 108724269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108724269 108757037 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 108724269 108757037).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108724269 108757037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108757037 108789805 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 108757037 108789805).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108757037 108789805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 108658733 108724269).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 108658733 ≤ 108691501)
    (by decide : 108691501 ≤ 108724269) block0 block1

theorem join_0_1 : (twinPrimeSegment 108724269 108789805).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 108724269 ≤ 108757037)
    (by decide : 108757037 ≤ 108789805) block2 block3

theorem join_1_0 : (twinPrimeSegment 108658733 108789805).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 108658733 ≤ 108724269)
    (by decide : 108724269 ≤ 108789805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 108658733 108789805).card = 470 := join_1_0

end S051C13
end Sude.GeneratedTwinScan
