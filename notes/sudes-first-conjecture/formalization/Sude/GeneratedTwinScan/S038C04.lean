import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80216109 80248877 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 80216109 80248877).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80216109 80248877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80248877 80281645 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 80248877 80281645).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80248877 80281645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80281645 80314413 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 80281645 80314413).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80281645 80314413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80314413 80347181 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 80314413 80347181).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80314413 80347181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 80216109 80281645).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 80216109 ≤ 80248877)
    (by decide : 80248877 ≤ 80281645) block0 block1

theorem join_0_1 : (twinPrimeSegment 80281645 80347181).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 80281645 ≤ 80314413)
    (by decide : 80314413 ≤ 80347181) block2 block3

theorem join_1_0 : (twinPrimeSegment 80216109 80347181).card = 523 := by
  simpa using combineTwinPrimeSegments (by decide : 80216109 ≤ 80281645)
    (by decide : 80281645 ≤ 80347181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 80216109 80347181).card = 523 := join_1_0

end S038C04
end Sude.GeneratedTwinScan
