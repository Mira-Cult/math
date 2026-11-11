import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73138221 73170989 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 73138221 73170989).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73138221 73170989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73170989 73203757 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 73170989 73203757).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73170989 73203757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73203757 73236525 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 73203757 73236525).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73203757 73236525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73236525 73269293 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 73236525 73269293).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73236525 73269293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 73138221 73203757).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 73138221 ≤ 73170989)
    (by decide : 73170989 ≤ 73203757) block0 block1

theorem join_0_1 : (twinPrimeSegment 73203757 73269293).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 73203757 ≤ 73236525)
    (by decide : 73236525 ≤ 73269293) block2 block3

theorem join_1_0 : (twinPrimeSegment 73138221 73269293).card = 547 := by
  simpa using combineTwinPrimeSegments (by decide : 73138221 ≤ 73203757)
    (by decide : 73203757 ≤ 73269293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 73138221 73269293).card = 547 := join_1_0

end S034C14
end Sude.GeneratedTwinScan
