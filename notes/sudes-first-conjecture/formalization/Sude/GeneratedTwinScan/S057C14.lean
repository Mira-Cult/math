import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121372717 121405485 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 121372717 121405485).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121372717 121405485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121405485 121438253 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 121405485 121438253).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121405485 121438253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121438253 121471021 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 121438253 121471021).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121438253 121471021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121471021 121503789 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 121471021 121503789).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121471021 121503789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 121372717 121438253).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 121372717 ≤ 121405485)
    (by decide : 121405485 ≤ 121438253) block0 block1

theorem join_0_1 : (twinPrimeSegment 121438253 121503789).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 121438253 ≤ 121471021)
    (by decide : 121471021 ≤ 121503789) block2 block3

theorem join_1_0 : (twinPrimeSegment 121372717 121503789).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 121372717 ≤ 121438253)
    (by decide : 121438253 ≤ 121503789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 121372717 121503789).card = 511 := join_1_0

end S057C14
end Sude.GeneratedTwinScan
