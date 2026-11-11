import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99614765 99647533 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 99614765 99647533).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99614765 99647533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99647533 99680301 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 99647533 99680301).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99647533 99680301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99680301 99713069 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 99680301 99713069).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99680301 99713069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99713069 99745837 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 99713069 99745837).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99713069 99745837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 99614765 99680301).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 99614765 ≤ 99647533)
    (by decide : 99647533 ≤ 99680301) block0 block1

theorem join_0_1 : (twinPrimeSegment 99680301 99745837).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 99680301 ≤ 99713069)
    (by decide : 99713069 ≤ 99745837) block2 block3

theorem join_1_0 : (twinPrimeSegment 99614765 99745837).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 99614765 ≤ 99680301)
    (by decide : 99680301 ≤ 99745837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 99614765 99745837).card = 487 := join_1_0

end S047C08
end Sude.GeneratedTwinScan
