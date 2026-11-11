import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66453549 66486317 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 66453549 66486317).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66453549 66486317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66486317 66519085 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 66486317 66519085).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66486317 66519085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66519085 66551853 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 66519085 66551853).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66519085 66551853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66551853 66584621 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 66551853 66584621).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66551853 66584621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 66453549 66519085).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 66453549 ≤ 66486317)
    (by decide : 66486317 ≤ 66519085) block0 block1

theorem join_0_1 : (twinPrimeSegment 66519085 66584621).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 66519085 ≤ 66551853)
    (by decide : 66551853 ≤ 66584621) block2 block3

theorem join_1_0 : (twinPrimeSegment 66453549 66584621).card = 543 := by
  simpa using combineTwinPrimeSegments (by decide : 66453549 ≤ 66519085)
    (by decide : 66519085 ≤ 66584621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 66453549 66584621).card = 543 := join_1_0

end S031C11
end Sude.GeneratedTwinScan
