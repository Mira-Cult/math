import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138018861 138051629 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 138018861 138051629).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138018861 138051629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138051629 138084397 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 138051629 138084397).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138051629 138084397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138084397 138117165 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 138084397 138117165).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138084397 138117165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138117165 138149933 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 138117165 138149933).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138117165 138149933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 138018861 138084397).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 138018861 ≤ 138051629)
    (by decide : 138051629 ≤ 138084397) block0 block1

theorem join_0_1 : (twinPrimeSegment 138084397 138149933).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 138084397 ≤ 138117165)
    (by decide : 138117165 ≤ 138149933) block2 block3

theorem join_1_0 : (twinPrimeSegment 138018861 138149933).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 138018861 ≤ 138084397)
    (by decide : 138084397 ≤ 138149933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 138018861 138149933).card = 473 := join_1_0

end S065C13
end Sude.GeneratedTwinScan
