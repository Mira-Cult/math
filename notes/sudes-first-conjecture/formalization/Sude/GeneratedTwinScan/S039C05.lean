import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82444333 82477101 = 147 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 82444333 82477101).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82444333 82477101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82477101 82509869 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 82477101 82509869).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82477101 82509869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82509869 82542637 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 82509869 82542637).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82509869 82542637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82542637 82575405 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 82542637 82575405).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82542637 82575405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 82444333 82509869).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 82444333 ≤ 82477101)
    (by decide : 82477101 ≤ 82509869) block0 block1

theorem join_0_1 : (twinPrimeSegment 82509869 82575405).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 82509869 ≤ 82542637)
    (by decide : 82542637 ≤ 82575405) block2 block3

theorem join_1_0 : (twinPrimeSegment 82444333 82575405).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 82444333 ≤ 82509869)
    (by decide : 82509869 ≤ 82575405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 82444333 82575405).card = 497 := join_1_0

end S039C05
end Sude.GeneratedTwinScan
