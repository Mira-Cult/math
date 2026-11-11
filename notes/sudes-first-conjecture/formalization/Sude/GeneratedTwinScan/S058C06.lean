import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122421293 122454061 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 122421293 122454061).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122421293 122454061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122454061 122486829 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 122454061 122486829).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122454061 122486829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122486829 122519597 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 122486829 122519597).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122486829 122519597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122519597 122552365 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 122519597 122552365).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122519597 122552365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 122421293 122486829).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 122421293 ≤ 122454061)
    (by decide : 122454061 ≤ 122486829) block0 block1

theorem join_0_1 : (twinPrimeSegment 122486829 122552365).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 122486829 ≤ 122519597)
    (by decide : 122519597 ≤ 122552365) block2 block3

theorem join_1_0 : (twinPrimeSegment 122421293 122552365).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 122421293 ≤ 122486829)
    (by decide : 122486829 ≤ 122552365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 122421293 122552365).card = 497 := join_1_0

end S058C06
end Sude.GeneratedTwinScan
