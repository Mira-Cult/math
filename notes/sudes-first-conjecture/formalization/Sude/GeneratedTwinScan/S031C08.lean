import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66060333 66093101 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 66060333 66093101).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66060333 66093101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66093101 66125869 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 66093101 66125869).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66093101 66125869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66125869 66158637 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 66125869 66158637).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66125869 66158637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66158637 66191405 = 150 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 66158637 66191405).card = 150 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66158637 66191405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 66060333 66125869).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 66060333 ≤ 66093101)
    (by decide : 66093101 ≤ 66125869) block0 block1

theorem join_0_1 : (twinPrimeSegment 66125869 66191405).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 66125869 ≤ 66158637)
    (by decide : 66158637 ≤ 66191405) block2 block3

theorem join_1_0 : (twinPrimeSegment 66060333 66191405).card = 533 := by
  simpa using combineTwinPrimeSegments (by decide : 66060333 ≤ 66125869)
    (by decide : 66125869 ≤ 66191405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 66060333 66191405).card = 533 := join_1_0

end S031C08
end Sude.GeneratedTwinScan
