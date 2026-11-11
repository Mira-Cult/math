import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92143661 92176429 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 92143661 92176429).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92143661 92176429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92176429 92209197 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 92176429 92209197).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92176429 92209197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92209197 92241965 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 92209197 92241965).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92209197 92241965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92241965 92274733 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 92241965 92274733).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92241965 92274733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 92143661 92209197).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 92143661 ≤ 92176429)
    (by decide : 92176429 ≤ 92209197) block0 block1

theorem join_0_1 : (twinPrimeSegment 92209197 92274733).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 92209197 ≤ 92241965)
    (by decide : 92241965 ≤ 92274733) block2 block3

theorem join_1_0 : (twinPrimeSegment 92143661 92274733).card = 521 := by
  simpa using combineTwinPrimeSegments (by decide : 92143661 ≤ 92209197)
    (by decide : 92209197 ≤ 92274733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 92143661 92274733).card = 521 := join_1_0

end S043C15
end Sude.GeneratedTwinScan
