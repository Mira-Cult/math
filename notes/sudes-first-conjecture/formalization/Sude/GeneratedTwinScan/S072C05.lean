import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151650349 151683117 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 151650349 151683117).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151650349 151683117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151683117 151715885 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 151683117 151715885).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151683117 151715885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151715885 151748653 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 151715885 151748653).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151715885 151748653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151748653 151781421 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 151748653 151781421).card = 101 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151748653 151781421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 151650349 151715885).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 151650349 ≤ 151683117)
    (by decide : 151683117 ≤ 151715885) block0 block1

theorem join_0_1 : (twinPrimeSegment 151715885 151781421).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 151715885 ≤ 151748653)
    (by decide : 151748653 ≤ 151781421) block2 block3

theorem join_1_0 : (twinPrimeSegment 151650349 151781421).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 151650349 ≤ 151715885)
    (by decide : 151715885 ≤ 151781421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 151650349 151781421).card = 476 := join_1_0

end S072C05
end Sude.GeneratedTwinScan
