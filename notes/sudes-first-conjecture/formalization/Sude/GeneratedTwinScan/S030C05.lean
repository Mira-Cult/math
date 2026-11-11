import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63569965 63602733 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 63569965 63602733).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63569965 63602733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63602733 63635501 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 63602733 63635501).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63602733 63635501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63635501 63668269 = 154 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 63635501 63668269).card = 154 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63635501 63668269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63668269 63701037 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 63668269 63701037).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63668269 63701037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 63569965 63635501).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 63569965 ≤ 63602733)
    (by decide : 63602733 ≤ 63635501) block0 block1

theorem join_0_1 : (twinPrimeSegment 63635501 63701037).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 63635501 ≤ 63668269)
    (by decide : 63668269 ≤ 63701037) block2 block3

theorem join_1_0 : (twinPrimeSegment 63569965 63701037).card = 550 := by
  simpa using combineTwinPrimeSegments (by decide : 63569965 ≤ 63635501)
    (by decide : 63635501 ≤ 63701037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 63569965 63701037).card = 550 := join_1_0

end S030C05
end Sude.GeneratedTwinScan
