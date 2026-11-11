import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132907053 132939821 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 132907053 132939821).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132907053 132939821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132939821 132972589 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 132939821 132972589).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132939821 132972589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132972589 133005357 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 132972589 133005357).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132972589 133005357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133005357 133038125 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 133005357 133038125).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133005357 133038125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 132907053 132972589).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 132907053 ≤ 132939821)
    (by decide : 132939821 ≤ 132972589) block0 block1

theorem join_0_1 : (twinPrimeSegment 132972589 133038125).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 132972589 ≤ 133005357)
    (by decide : 133005357 ≤ 133038125) block2 block3

theorem join_1_0 : (twinPrimeSegment 132907053 133038125).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 132907053 ≤ 132972589)
    (by decide : 132972589 ≤ 133038125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 132907053 133038125).card = 506 := join_1_0

end S063C06
end Sude.GeneratedTwinScan
