import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103546925 103579693 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 103546925 103579693).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103546925 103579693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103579693 103612461 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 103579693 103612461).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103579693 103612461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103612461 103645229 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 103612461 103645229).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103612461 103645229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103645229 103677997 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 103645229 103677997).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103645229 103677997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 103546925 103612461).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 103546925 ≤ 103579693)
    (by decide : 103579693 ≤ 103612461) block0 block1

theorem join_0_1 : (twinPrimeSegment 103612461 103677997).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 103612461 ≤ 103645229)
    (by decide : 103645229 ≤ 103677997) block2 block3

theorem join_1_0 : (twinPrimeSegment 103546925 103677997).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 103546925 ≤ 103612461)
    (by decide : 103612461 ≤ 103677997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 103546925 103677997).card = 512 := join_1_0

end S049C06
end Sude.GeneratedTwinScan
