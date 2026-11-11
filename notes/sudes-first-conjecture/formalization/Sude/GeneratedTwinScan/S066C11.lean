import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139853869 139886637 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 139853869 139886637).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139853869 139886637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139886637 139919405 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 139886637 139919405).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139886637 139919405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139919405 139952173 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 139919405 139952173).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139919405 139952173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139952173 139984941 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 139952173 139984941).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139952173 139984941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 139853869 139919405).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 139853869 ≤ 139886637)
    (by decide : 139886637 ≤ 139919405) block0 block1

theorem join_0_1 : (twinPrimeSegment 139919405 139984941).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 139919405 ≤ 139952173)
    (by decide : 139952173 ≤ 139984941) block2 block3

theorem join_1_0 : (twinPrimeSegment 139853869 139984941).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 139853869 ≤ 139919405)
    (by decide : 139919405 ≤ 139984941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 139853869 139984941).card = 476 := join_1_0

end S066C11
end Sude.GeneratedTwinScan
