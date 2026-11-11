import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66846765 66879533 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 66846765 66879533).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66846765 66879533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66879533 66912301 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 66879533 66912301).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66879533 66912301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66912301 66945069 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 66912301 66945069).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66912301 66945069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66945069 66977837 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 66945069 66977837).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66945069 66977837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 66846765 66912301).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 66846765 ≤ 66879533)
    (by decide : 66879533 ≤ 66912301) block0 block1

theorem join_0_1 : (twinPrimeSegment 66912301 66977837).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 66912301 ≤ 66945069)
    (by decide : 66945069 ≤ 66977837) block2 block3

theorem join_1_0 : (twinPrimeSegment 66846765 66977837).card = 569 := by
  simpa using combineTwinPrimeSegments (by decide : 66846765 ≤ 66912301)
    (by decide : 66912301 ≤ 66977837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 66846765 66977837).card = 569 := join_1_0

end S031C14
end Sude.GeneratedTwinScan
