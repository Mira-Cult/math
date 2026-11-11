import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129630253 129663021 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 129630253 129663021).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129630253 129663021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129663021 129695789 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 129663021 129695789).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129663021 129695789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129695789 129728557 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 129695789 129728557).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129695789 129728557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129728557 129761325 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 129728557 129761325).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129728557 129761325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 129630253 129695789).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 129630253 ≤ 129663021)
    (by decide : 129663021 ≤ 129695789) block0 block1

theorem join_0_1 : (twinPrimeSegment 129695789 129761325).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 129695789 ≤ 129728557)
    (by decide : 129728557 ≤ 129761325) block2 block3

theorem join_1_0 : (twinPrimeSegment 129630253 129761325).card = 537 := by
  simpa using combineTwinPrimeSegments (by decide : 129630253 ≤ 129695789)
    (by decide : 129695789 ≤ 129761325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 129630253 129761325).card = 537 := join_1_0

end S061C13
end Sude.GeneratedTwinScan
