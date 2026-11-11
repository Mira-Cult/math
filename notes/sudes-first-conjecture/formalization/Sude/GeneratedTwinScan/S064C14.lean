import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136052781 136085549 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 136052781 136085549).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136052781 136085549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136085549 136118317 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 136085549 136118317).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136085549 136118317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136118317 136151085 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 136118317 136151085).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136118317 136151085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136151085 136183853 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 136151085 136183853).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136151085 136183853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 136052781 136118317).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 136052781 ≤ 136085549)
    (by decide : 136085549 ≤ 136118317) block0 block1

theorem join_0_1 : (twinPrimeSegment 136118317 136183853).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 136118317 ≤ 136151085)
    (by decide : 136151085 ≤ 136183853) block2 block3

theorem join_1_0 : (twinPrimeSegment 136052781 136183853).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 136052781 ≤ 136118317)
    (by decide : 136118317 ≤ 136183853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 136052781 136183853).card = 489 := join_1_0

end S064C14
end Sude.GeneratedTwinScan
