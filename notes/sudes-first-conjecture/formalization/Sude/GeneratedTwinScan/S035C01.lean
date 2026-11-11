import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73531437 73564205 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 73531437 73564205).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73531437 73564205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73564205 73596973 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 73564205 73596973).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73564205 73596973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73596973 73629741 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 73596973 73629741).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73596973 73629741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73629741 73662509 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 73629741 73662509).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73629741 73662509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 73531437 73596973).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 73531437 ≤ 73564205)
    (by decide : 73564205 ≤ 73596973) block0 block1

theorem join_0_1 : (twinPrimeSegment 73596973 73662509).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 73596973 ≤ 73629741)
    (by decide : 73629741 ≤ 73662509) block2 block3

theorem join_1_0 : (twinPrimeSegment 73531437 73662509).card = 515 := by
  simpa using combineTwinPrimeSegments (by decide : 73531437 ≤ 73596973)
    (by decide : 73596973 ≤ 73662509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 73531437 73662509).card = 515 := join_1_0

end S035C01
end Sude.GeneratedTwinScan
