import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132382765 132415533 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 132382765 132415533).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132382765 132415533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132415533 132448301 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 132415533 132448301).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132415533 132448301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132448301 132481069 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 132448301 132481069).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132448301 132481069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132481069 132513837 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 132481069 132513837).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132481069 132513837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 132382765 132448301).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 132382765 ≤ 132415533)
    (by decide : 132415533 ≤ 132448301) block0 block1

theorem join_0_1 : (twinPrimeSegment 132448301 132513837).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 132448301 ≤ 132481069)
    (by decide : 132481069 ≤ 132513837) block2 block3

theorem join_1_0 : (twinPrimeSegment 132382765 132513837).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 132382765 ≤ 132448301)
    (by decide : 132448301 ≤ 132513837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 132382765 132513837).card = 495 := join_1_0

end S063C02
end Sude.GeneratedTwinScan
