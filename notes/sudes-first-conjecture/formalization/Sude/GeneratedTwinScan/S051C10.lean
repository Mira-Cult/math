import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108265517 108298285 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 108265517 108298285).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108265517 108298285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108298285 108331053 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 108298285 108331053).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108298285 108331053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108331053 108363821 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 108331053 108363821).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108331053 108363821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108363821 108396589 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 108363821 108396589).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108363821 108396589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 108265517 108331053).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 108265517 ≤ 108298285)
    (by decide : 108298285 ≤ 108331053) block0 block1

theorem join_0_1 : (twinPrimeSegment 108331053 108396589).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 108331053 ≤ 108363821)
    (by decide : 108363821 ≤ 108396589) block2 block3

theorem join_1_0 : (twinPrimeSegment 108265517 108396589).card = 545 := by
  simpa using combineTwinPrimeSegments (by decide : 108265517 ≤ 108331053)
    (by decide : 108331053 ≤ 108396589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 108265517 108396589).card = 545 := join_1_0

end S051C10
end Sude.GeneratedTwinScan
