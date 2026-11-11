import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110624813 110657581 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 110624813 110657581).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110624813 110657581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110657581 110690349 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 110657581 110690349).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110657581 110690349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110690349 110723117 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 110690349 110723117).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110690349 110723117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110723117 110755885 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 110723117 110755885).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110723117 110755885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 110624813 110690349).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 110624813 ≤ 110657581)
    (by decide : 110657581 ≤ 110690349) block0 block1

theorem join_0_1 : (twinPrimeSegment 110690349 110755885).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 110690349 ≤ 110723117)
    (by decide : 110723117 ≤ 110755885) block2 block3

theorem join_1_0 : (twinPrimeSegment 110624813 110755885).card = 535 := by
  simpa using combineTwinPrimeSegments (by decide : 110624813 ≤ 110690349)
    (by decide : 110690349 ≤ 110755885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 110624813 110755885).card = 535 := join_1_0

end S052C12
end Sude.GeneratedTwinScan
