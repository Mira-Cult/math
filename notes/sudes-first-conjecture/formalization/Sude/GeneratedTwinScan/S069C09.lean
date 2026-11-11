import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145883181 145915949 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 145883181 145915949).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145883181 145915949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145915949 145948717 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 145915949 145948717).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145915949 145948717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145948717 145981485 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 145948717 145981485).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145948717 145981485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145981485 146014253 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 145981485 146014253).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145981485 146014253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 145883181 145948717).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 145883181 ≤ 145915949)
    (by decide : 145915949 ≤ 145948717) block0 block1

theorem join_0_1 : (twinPrimeSegment 145948717 146014253).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 145948717 ≤ 145981485)
    (by decide : 145981485 ≤ 146014253) block2 block3

theorem join_1_0 : (twinPrimeSegment 145883181 146014253).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 145883181 ≤ 145948717)
    (by decide : 145948717 ≤ 146014253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 145883181 146014253).card = 502 := join_1_0

end S069C09
end Sude.GeneratedTwinScan
