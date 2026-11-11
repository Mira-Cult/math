import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99221549 99254317 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 99221549 99254317).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99221549 99254317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99254317 99287085 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 99254317 99287085).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99254317 99287085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99287085 99319853 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 99287085 99319853).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99287085 99319853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99319853 99352621 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 99319853 99352621).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99319853 99352621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 99221549 99287085).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 99221549 ≤ 99254317)
    (by decide : 99254317 ≤ 99287085) block0 block1

theorem join_0_1 : (twinPrimeSegment 99287085 99352621).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 99287085 ≤ 99319853)
    (by decide : 99319853 ≤ 99352621) block2 block3

theorem join_1_0 : (twinPrimeSegment 99221549 99352621).card = 519 := by
  simpa using combineTwinPrimeSegments (by decide : 99221549 ≤ 99287085)
    (by decide : 99287085 ≤ 99352621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 99221549 99352621).card = 519 := join_1_0

end S047C05
end Sude.GeneratedTwinScan
