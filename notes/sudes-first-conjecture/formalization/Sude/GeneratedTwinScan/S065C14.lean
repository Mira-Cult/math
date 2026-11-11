import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138149933 138182701 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 138149933 138182701).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138149933 138182701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138182701 138215469 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 138182701 138215469).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138182701 138215469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138215469 138248237 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 138215469 138248237).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138215469 138248237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138248237 138281005 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 138248237 138281005).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138248237 138281005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 138149933 138215469).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 138149933 ≤ 138182701)
    (by decide : 138182701 ≤ 138215469) block0 block1

theorem join_0_1 : (twinPrimeSegment 138215469 138281005).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 138215469 ≤ 138248237)
    (by decide : 138248237 ≤ 138281005) block2 block3

theorem join_1_0 : (twinPrimeSegment 138149933 138281005).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 138149933 ≤ 138215469)
    (by decide : 138215469 ≤ 138281005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 138149933 138281005).card = 487 := join_1_0

end S065C14
end Sude.GeneratedTwinScan
