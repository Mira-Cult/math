import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87162925 87195693 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 87162925 87195693).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87162925 87195693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87195693 87228461 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 87195693 87228461).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87195693 87228461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87228461 87261229 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 87228461 87261229).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87228461 87261229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87261229 87293997 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 87261229 87293997).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87261229 87293997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 87162925 87228461).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 87162925 ≤ 87195693)
    (by decide : 87195693 ≤ 87228461) block0 block1

theorem join_0_1 : (twinPrimeSegment 87228461 87293997).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 87228461 ≤ 87261229)
    (by decide : 87261229 ≤ 87293997) block2 block3

theorem join_1_0 : (twinPrimeSegment 87162925 87293997).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 87162925 ≤ 87228461)
    (by decide : 87228461 ≤ 87293997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 87162925 87293997).card = 499 := join_1_0

end S041C09
end Sude.GeneratedTwinScan
