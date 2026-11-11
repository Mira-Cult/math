import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135397421 135430189 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 135397421 135430189).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135397421 135430189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135430189 135462957 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 135430189 135462957).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135430189 135462957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135462957 135495725 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 135462957 135495725).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135462957 135495725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135495725 135528493 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 135495725 135528493).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135495725 135528493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 135397421 135462957).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 135397421 ≤ 135430189)
    (by decide : 135430189 ≤ 135462957) block0 block1

theorem join_0_1 : (twinPrimeSegment 135462957 135528493).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 135462957 ≤ 135495725)
    (by decide : 135495725 ≤ 135528493) block2 block3

theorem join_1_0 : (twinPrimeSegment 135397421 135528493).card = 517 := by
  simpa using combineTwinPrimeSegments (by decide : 135397421 ≤ 135462957)
    (by decide : 135462957 ≤ 135528493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 135397421 135528493).card = 517 := join_1_0

end S064C09
end Sude.GeneratedTwinScan
