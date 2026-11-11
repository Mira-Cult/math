import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152829997 152862765 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 152829997 152862765).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152829997 152862765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152862765 152895533 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 152862765 152895533).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152862765 152895533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152895533 152928301 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 152895533 152928301).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152895533 152928301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152928301 152961069 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 152928301 152961069).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152928301 152961069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 152829997 152895533).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 152829997 ≤ 152862765)
    (by decide : 152862765 ≤ 152895533) block0 block1

theorem join_0_1 : (twinPrimeSegment 152895533 152961069).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 152895533 ≤ 152928301)
    (by decide : 152928301 ≤ 152961069) block2 block3

theorem join_1_0 : (twinPrimeSegment 152829997 152961069).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 152829997 ≤ 152895533)
    (by decide : 152895533 ≤ 152961069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 152829997 152961069).card = 468 := join_1_0

end S072C14
end Sude.GeneratedTwinScan
