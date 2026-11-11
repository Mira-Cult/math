import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75497517 75530285 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 75497517 75530285).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75497517 75530285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75530285 75563053 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 75530285 75563053).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75530285 75563053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75563053 75595821 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 75563053 75595821).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75563053 75595821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75595821 75628589 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 75595821 75628589).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75595821 75628589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 75497517 75563053).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 75497517 ≤ 75530285)
    (by decide : 75530285 ≤ 75563053) block0 block1

theorem join_0_1 : (twinPrimeSegment 75563053 75628589).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 75563053 ≤ 75595821)
    (by decide : 75595821 ≤ 75628589) block2 block3

theorem join_1_0 : (twinPrimeSegment 75497517 75628589).card = 532 := by
  simpa using combineTwinPrimeSegments (by decide : 75497517 ≤ 75563053)
    (by decide : 75563053 ≤ 75628589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 75497517 75628589).card = 532 := join_1_0

end S036C00
end Sude.GeneratedTwinScan
