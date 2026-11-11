import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115998765 116031533 = 148 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 115998765 116031533).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115998765 116031533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116031533 116064301 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 116031533 116064301).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116031533 116064301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116064301 116097069 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 116064301 116097069).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116064301 116097069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116097069 116129837 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 116097069 116129837).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116097069 116129837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 115998765 116064301).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 115998765 ≤ 116031533)
    (by decide : 116031533 ≤ 116064301) block0 block1

theorem join_0_1 : (twinPrimeSegment 116064301 116129837).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 116064301 ≤ 116097069)
    (by decide : 116097069 ≤ 116129837) block2 block3

theorem join_1_0 : (twinPrimeSegment 115998765 116129837).card = 521 := by
  simpa using combineTwinPrimeSegments (by decide : 115998765 ≤ 116064301)
    (by decide : 116064301 ≤ 116129837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 115998765 116129837).card = 521 := join_1_0

end S055C05
end Sude.GeneratedTwinScan
