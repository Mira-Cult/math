import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82313261 82346029 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 82313261 82346029).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82313261 82346029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82346029 82378797 = 149 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 82346029 82378797).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82346029 82378797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82378797 82411565 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 82378797 82411565).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82378797 82411565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82411565 82444333 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 82411565 82444333).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82411565 82444333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 82313261 82378797).card = 287 := by
  simpa using combineTwinPrimeSegments (by decide : 82313261 ≤ 82346029)
    (by decide : 82346029 ≤ 82378797) block0 block1

theorem join_0_1 : (twinPrimeSegment 82378797 82444333).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 82378797 ≤ 82411565)
    (by decide : 82411565 ≤ 82444333) block2 block3

theorem join_1_0 : (twinPrimeSegment 82313261 82444333).card = 543 := by
  simpa using combineTwinPrimeSegments (by decide : 82313261 ≤ 82378797)
    (by decide : 82378797 ≤ 82444333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 82313261 82444333).card = 543 := join_1_0

end S039C04
end Sude.GeneratedTwinScan
