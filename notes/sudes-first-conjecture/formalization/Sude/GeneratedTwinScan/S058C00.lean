import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121634861 121667629 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 121634861 121667629).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121634861 121667629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121667629 121700397 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 121667629 121700397).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121667629 121700397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121700397 121733165 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 121700397 121733165).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121700397 121733165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121733165 121765933 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 121733165 121765933).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121733165 121765933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 121634861 121700397).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 121634861 ≤ 121667629)
    (by decide : 121667629 ≤ 121700397) block0 block1

theorem join_0_1 : (twinPrimeSegment 121700397 121765933).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 121700397 ≤ 121733165)
    (by decide : 121733165 ≤ 121765933) block2 block3

theorem join_1_0 : (twinPrimeSegment 121634861 121765933).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 121634861 ≤ 121700397)
    (by decide : 121700397 ≤ 121765933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 121634861 121765933).card = 506 := join_1_0

end S058C00
end Sude.GeneratedTwinScan
