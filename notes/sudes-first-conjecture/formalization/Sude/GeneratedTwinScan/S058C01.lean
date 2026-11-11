import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121765933 121798701 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 121765933 121798701).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121765933 121798701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121798701 121831469 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 121798701 121831469).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121798701 121831469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121831469 121864237 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 121831469 121864237).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121831469 121864237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121864237 121897005 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 121864237 121897005).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121864237 121897005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 121765933 121831469).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 121765933 ≤ 121798701)
    (by decide : 121798701 ≤ 121831469) block0 block1

theorem join_0_1 : (twinPrimeSegment 121831469 121897005).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 121831469 ≤ 121864237)
    (by decide : 121864237 ≤ 121897005) block2 block3

theorem join_1_0 : (twinPrimeSegment 121765933 121897005).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 121765933 ≤ 121831469)
    (by decide : 121831469 ≤ 121897005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 121765933 121897005).card = 506 := join_1_0

end S058C01
end Sude.GeneratedTwinScan
