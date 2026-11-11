import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96075821 96108589 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 96075821 96108589).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96075821 96108589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96108589 96141357 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 96108589 96141357).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96108589 96141357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96141357 96174125 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 96141357 96174125).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96141357 96174125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96174125 96206893 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 96174125 96206893).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96174125 96206893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 96075821 96141357).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 96075821 ≤ 96108589)
    (by decide : 96108589 ≤ 96141357) block0 block1

theorem join_0_1 : (twinPrimeSegment 96141357 96206893).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 96141357 ≤ 96174125)
    (by decide : 96174125 ≤ 96206893) block2 block3

theorem join_1_0 : (twinPrimeSegment 96075821 96206893).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 96075821 ≤ 96141357)
    (by decide : 96141357 ≤ 96206893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 96075821 96206893).card = 496 := join_1_0

end S045C13
end Sude.GeneratedTwinScan
