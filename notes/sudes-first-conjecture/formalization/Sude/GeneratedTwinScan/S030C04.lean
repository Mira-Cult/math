import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63438893 63471661 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 63438893 63471661).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63438893 63471661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63471661 63504429 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 63471661 63504429).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63471661 63504429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63504429 63537197 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 63504429 63537197).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63504429 63537197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63537197 63569965 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 63537197 63569965).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63537197 63569965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 63438893 63504429).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 63438893 ≤ 63471661)
    (by decide : 63471661 ≤ 63504429) block0 block1

theorem join_0_1 : (twinPrimeSegment 63504429 63569965).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 63504429 ≤ 63537197)
    (by decide : 63537197 ≤ 63569965) block2 block3

theorem join_1_0 : (twinPrimeSegment 63438893 63569965).card = 536 := by
  simpa using combineTwinPrimeSegments (by decide : 63438893 ≤ 63504429)
    (by decide : 63504429 ≤ 63569965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 63438893 63569965).card = 536 := join_1_0

end S030C04
end Sude.GeneratedTwinScan
