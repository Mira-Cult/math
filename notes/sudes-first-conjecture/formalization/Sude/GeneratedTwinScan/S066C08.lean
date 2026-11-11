import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139460653 139493421 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 139460653 139493421).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139460653 139493421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139493421 139526189 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 139493421 139526189).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139493421 139526189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139526189 139558957 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 139526189 139558957).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139526189 139558957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139558957 139591725 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 139558957 139591725).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139558957 139591725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 139460653 139526189).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 139460653 ≤ 139493421)
    (by decide : 139493421 ≤ 139526189) block0 block1

theorem join_0_1 : (twinPrimeSegment 139526189 139591725).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 139526189 ≤ 139558957)
    (by decide : 139558957 ≤ 139591725) block2 block3

theorem join_1_0 : (twinPrimeSegment 139460653 139591725).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 139460653 ≤ 139526189)
    (by decide : 139526189 ≤ 139591725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 139460653 139591725).card = 496 := join_1_0

end S066C08
end Sude.GeneratedTwinScan
