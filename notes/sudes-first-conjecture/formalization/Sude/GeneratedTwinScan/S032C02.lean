import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67371053 67403821 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 67371053 67403821).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67371053 67403821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67403821 67436589 = 149 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 67403821 67436589).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67403821 67436589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67436589 67469357 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 67436589 67469357).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67436589 67469357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67469357 67502125 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 67469357 67502125).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67469357 67502125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 67371053 67436589).card = 287 := by
  simpa using combineTwinPrimeSegments (by decide : 67371053 ≤ 67403821)
    (by decide : 67403821 ≤ 67436589) block0 block1

theorem join_0_1 : (twinPrimeSegment 67436589 67502125).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 67436589 ≤ 67469357)
    (by decide : 67469357 ≤ 67502125) block2 block3

theorem join_1_0 : (twinPrimeSegment 67371053 67502125).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 67371053 ≤ 67436589)
    (by decide : 67436589 ≤ 67502125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 67371053 67502125).card = 549 := join_1_0

end S032C02
end Sude.GeneratedTwinScan
