import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78250029 78282797 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 78250029 78282797).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78250029 78282797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78282797 78315565 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 78282797 78315565).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78282797 78315565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78315565 78348333 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 78315565 78348333).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78315565 78348333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78348333 78381101 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 78348333 78381101).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78348333 78381101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 78250029 78315565).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 78250029 ≤ 78282797)
    (by decide : 78282797 ≤ 78315565) block0 block1

theorem join_0_1 : (twinPrimeSegment 78315565 78381101).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 78315565 ≤ 78348333)
    (by decide : 78348333 ≤ 78381101) block2 block3

theorem join_1_0 : (twinPrimeSegment 78250029 78381101).card = 518 := by
  simpa using combineTwinPrimeSegments (by decide : 78250029 ≤ 78315565)
    (by decide : 78315565 ≤ 78381101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 78250029 78381101).card = 518 := join_1_0

end S037C05
end Sude.GeneratedTwinScan
