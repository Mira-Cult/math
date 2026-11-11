import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91881517 91914285 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 91881517 91914285).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91881517 91914285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91914285 91947053 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 91914285 91947053).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91914285 91947053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91947053 91979821 = 146 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 91947053 91979821).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91947053 91979821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91979821 92012589 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 91979821 92012589).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91979821 92012589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 91881517 91947053).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 91881517 ≤ 91914285)
    (by decide : 91914285 ≤ 91947053) block0 block1

theorem join_0_1 : (twinPrimeSegment 91947053 92012589).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 91947053 ≤ 91979821)
    (by decide : 91979821 ≤ 92012589) block2 block3

theorem join_1_0 : (twinPrimeSegment 91881517 92012589).card = 526 := by
  simpa using combineTwinPrimeSegments (by decide : 91881517 ≤ 91947053)
    (by decide : 91947053 ≤ 92012589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 91881517 92012589).card = 526 := join_1_0

end S043C13
end Sude.GeneratedTwinScan
