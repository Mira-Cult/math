import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116654125 116686893 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 116654125 116686893).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116654125 116686893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116686893 116719661 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 116686893 116719661).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116686893 116719661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116719661 116752429 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 116719661 116752429).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116719661 116752429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116752429 116785197 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 116752429 116785197).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116752429 116785197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 116654125 116719661).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 116654125 ≤ 116686893)
    (by decide : 116686893 ≤ 116719661) block0 block1

theorem join_0_1 : (twinPrimeSegment 116719661 116785197).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 116719661 ≤ 116752429)
    (by decide : 116752429 ≤ 116785197) block2 block3

theorem join_1_0 : (twinPrimeSegment 116654125 116785197).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 116654125 ≤ 116719661)
    (by decide : 116719661 ≤ 116785197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 116654125 116785197).card = 508 := join_1_0

end S055C10
end Sude.GeneratedTwinScan
