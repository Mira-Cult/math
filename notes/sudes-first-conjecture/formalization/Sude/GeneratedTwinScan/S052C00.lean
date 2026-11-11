import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109051949 109084717 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 109051949 109084717).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109051949 109084717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109084717 109117485 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 109084717 109117485).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109084717 109117485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109117485 109150253 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 109117485 109150253).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109117485 109150253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109150253 109183021 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 109150253 109183021).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109150253 109183021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 109051949 109117485).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 109051949 ≤ 109084717)
    (by decide : 109084717 ≤ 109117485) block0 block1

theorem join_0_1 : (twinPrimeSegment 109117485 109183021).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 109117485 ≤ 109150253)
    (by decide : 109150253 ≤ 109183021) block2 block3

theorem join_1_0 : (twinPrimeSegment 109051949 109183021).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 109051949 ≤ 109117485)
    (by decide : 109117485 ≤ 109183021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 109051949 109183021).card = 479 := join_1_0

end S052C00
end Sude.GeneratedTwinScan
