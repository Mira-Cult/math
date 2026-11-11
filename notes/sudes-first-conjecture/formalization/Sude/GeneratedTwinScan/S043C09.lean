import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91357229 91389997 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 91357229 91389997).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91357229 91389997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91389997 91422765 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 91389997 91422765).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91389997 91422765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91422765 91455533 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 91422765 91455533).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91422765 91455533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91455533 91488301 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 91455533 91488301).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91455533 91488301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 91357229 91422765).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 91357229 ≤ 91389997)
    (by decide : 91389997 ≤ 91422765) block0 block1

theorem join_0_1 : (twinPrimeSegment 91422765 91488301).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 91422765 ≤ 91455533)
    (by decide : 91455533 ≤ 91488301) block2 block3

theorem join_1_0 : (twinPrimeSegment 91357229 91488301).card = 514 := by
  simpa using combineTwinPrimeSegments (by decide : 91357229 ≤ 91422765)
    (by decide : 91422765 ≤ 91488301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 91357229 91488301).card = 514 := join_1_0

end S043C09
end Sude.GeneratedTwinScan
