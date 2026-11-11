import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135135277 135168045 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 135135277 135168045).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135135277 135168045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135168045 135200813 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 135168045 135200813).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135168045 135200813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135200813 135233581 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 135200813 135233581).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135200813 135233581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135233581 135266349 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 135233581 135266349).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135233581 135266349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 135135277 135200813).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 135135277 ≤ 135168045)
    (by decide : 135168045 ≤ 135200813) block0 block1

theorem join_0_1 : (twinPrimeSegment 135200813 135266349).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 135200813 ≤ 135233581)
    (by decide : 135233581 ≤ 135266349) block2 block3

theorem join_1_0 : (twinPrimeSegment 135135277 135266349).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 135135277 ≤ 135200813)
    (by decide : 135200813 ≤ 135266349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 135135277 135266349).card = 501 := join_1_0

end S064C07
end Sude.GeneratedTwinScan
