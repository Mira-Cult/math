import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64094253 64127021 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 64094253 64127021).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64094253 64127021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64127021 64159789 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 64127021 64159789).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64127021 64159789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64159789 64192557 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 64159789 64192557).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64159789 64192557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64192557 64225325 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 64192557 64225325).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64192557 64225325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 64094253 64159789).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 64094253 ≤ 64127021)
    (by decide : 64127021 ≤ 64159789) block0 block1

theorem join_0_1 : (twinPrimeSegment 64159789 64225325).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 64159789 ≤ 64192557)
    (by decide : 64192557 ≤ 64225325) block2 block3

theorem join_1_0 : (twinPrimeSegment 64094253 64225325).card = 544 := by
  simpa using combineTwinPrimeSegments (by decide : 64094253 ≤ 64159789)
    (by decide : 64159789 ≤ 64225325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 64094253 64225325).card = 544 := join_1_0

end S030C09
end Sude.GeneratedTwinScan
