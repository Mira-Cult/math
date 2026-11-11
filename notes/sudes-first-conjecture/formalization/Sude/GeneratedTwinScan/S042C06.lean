import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88866861 88899629 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 88866861 88899629).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88866861 88899629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88899629 88932397 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 88899629 88932397).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88899629 88932397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88932397 88965165 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 88932397 88965165).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88932397 88965165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88965165 88997933 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 88965165 88997933).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88965165 88997933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 88866861 88932397).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 88866861 ≤ 88899629)
    (by decide : 88899629 ≤ 88932397) block0 block1

theorem join_0_1 : (twinPrimeSegment 88932397 88997933).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 88932397 ≤ 88965165)
    (by decide : 88965165 ≤ 88997933) block2 block3

theorem join_1_0 : (twinPrimeSegment 88866861 88997933).card = 547 := by
  simpa using combineTwinPrimeSegments (by decide : 88866861 ≤ 88932397)
    (by decide : 88932397 ≤ 88997933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 88866861 88997933).card = 547 := join_1_0

end S042C06
end Sude.GeneratedTwinScan
