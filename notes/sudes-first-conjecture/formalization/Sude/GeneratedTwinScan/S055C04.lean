import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115867693 115900461 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 115867693 115900461).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115867693 115900461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115900461 115933229 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 115900461 115933229).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115900461 115933229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115933229 115965997 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 115933229 115965997).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115933229 115965997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115965997 115998765 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 115965997 115998765).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115965997 115998765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 115867693 115933229).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 115867693 ≤ 115900461)
    (by decide : 115900461 ≤ 115933229) block0 block1

theorem join_0_1 : (twinPrimeSegment 115933229 115998765).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 115933229 ≤ 115965997)
    (by decide : 115965997 ≤ 115998765) block2 block3

theorem join_1_0 : (twinPrimeSegment 115867693 115998765).card = 510 := by
  simpa using combineTwinPrimeSegments (by decide : 115867693 ≤ 115933229)
    (by decide : 115933229 ≤ 115998765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 115867693 115998765).card = 510 := join_1_0

end S055C04
end Sude.GeneratedTwinScan
