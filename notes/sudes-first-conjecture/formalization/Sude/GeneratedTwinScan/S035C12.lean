import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74973229 75005997 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 74973229 75005997).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74973229 75005997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75005997 75038765 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 75005997 75038765).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75005997 75038765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75038765 75071533 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 75038765 75071533).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75038765 75071533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75071533 75104301 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 75071533 75104301).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75071533 75104301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 74973229 75038765).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 74973229 ≤ 75005997)
    (by decide : 75005997 ≤ 75038765) block0 block1

theorem join_0_1 : (twinPrimeSegment 75038765 75104301).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 75038765 ≤ 75071533)
    (by decide : 75071533 ≤ 75104301) block2 block3

theorem join_1_0 : (twinPrimeSegment 74973229 75104301).card = 519 := by
  simpa using combineTwinPrimeSegments (by decide : 74973229 ≤ 75038765)
    (by decide : 75038765 ≤ 75104301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 74973229 75104301).card = 519 := join_1_0

end S035C12
end Sude.GeneratedTwinScan
