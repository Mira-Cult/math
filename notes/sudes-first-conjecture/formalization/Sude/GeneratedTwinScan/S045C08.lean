import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95420461 95453229 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 95420461 95453229).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95420461 95453229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95453229 95485997 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 95453229 95485997).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95453229 95485997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95485997 95518765 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 95485997 95518765).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95485997 95518765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95518765 95551533 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 95518765 95551533).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95518765 95551533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 95420461 95485997).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 95420461 ≤ 95453229)
    (by decide : 95453229 ≤ 95485997) block0 block1

theorem join_0_1 : (twinPrimeSegment 95485997 95551533).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 95485997 ≤ 95518765)
    (by decide : 95518765 ≤ 95551533) block2 block3

theorem join_1_0 : (twinPrimeSegment 95420461 95551533).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 95420461 ≤ 95485997)
    (by decide : 95485997 ≤ 95551533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 95420461 95551533).card = 549 := join_1_0

end S045C08
end Sude.GeneratedTwinScan
