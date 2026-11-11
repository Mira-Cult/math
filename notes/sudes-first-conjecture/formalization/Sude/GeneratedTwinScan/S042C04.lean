import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88604717 88637485 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 88604717 88637485).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88604717 88637485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88637485 88670253 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 88637485 88670253).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88637485 88670253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88670253 88703021 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 88670253 88703021).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88670253 88703021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88703021 88735789 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 88703021 88735789).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88703021 88735789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 88604717 88670253).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 88604717 ≤ 88637485)
    (by decide : 88637485 ≤ 88670253) block0 block1

theorem join_0_1 : (twinPrimeSegment 88670253 88735789).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 88670253 ≤ 88703021)
    (by decide : 88703021 ≤ 88735789) block2 block3

theorem join_1_0 : (twinPrimeSegment 88604717 88735789).card = 532 := by
  simpa using combineTwinPrimeSegments (by decide : 88604717 ≤ 88670253)
    (by decide : 88670253 ≤ 88735789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 88604717 88735789).card = 532 := join_1_0

end S042C04
end Sude.GeneratedTwinScan
