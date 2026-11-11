import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140116013 140148781 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 140116013 140148781).card = 107 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140116013 140148781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140148781 140181549 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 140148781 140181549).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140148781 140181549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140181549 140214317 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 140181549 140214317).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140181549 140214317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140214317 140247085 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 140214317 140247085).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140214317 140247085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 140116013 140181549).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 140116013 ≤ 140148781)
    (by decide : 140148781 ≤ 140181549) block0 block1

theorem join_0_1 : (twinPrimeSegment 140181549 140247085).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 140181549 ≤ 140214317)
    (by decide : 140214317 ≤ 140247085) block2 block3

theorem join_1_0 : (twinPrimeSegment 140116013 140247085).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 140116013 ≤ 140181549)
    (by decide : 140181549 ≤ 140247085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 140116013 140247085).card = 467 := join_1_0

end S066C13
end Sude.GeneratedTwinScan
