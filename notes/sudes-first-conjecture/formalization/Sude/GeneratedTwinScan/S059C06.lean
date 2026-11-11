import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124518445 124551213 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 124518445 124551213).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124518445 124551213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124551213 124583981 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 124551213 124583981).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124551213 124583981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124583981 124616749 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 124583981 124616749).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124583981 124616749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124616749 124649517 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 124616749 124649517).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124616749 124649517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 124518445 124583981).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 124518445 ≤ 124551213)
    (by decide : 124551213 ≤ 124583981) block0 block1

theorem join_0_1 : (twinPrimeSegment 124583981 124649517).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 124583981 ≤ 124616749)
    (by decide : 124616749 ≤ 124649517) block2 block3

theorem join_1_0 : (twinPrimeSegment 124518445 124649517).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 124518445 ≤ 124583981)
    (by decide : 124583981 ≤ 124649517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 124518445 124649517).card = 481 := join_1_0

end S059C06
end Sude.GeneratedTwinScan
