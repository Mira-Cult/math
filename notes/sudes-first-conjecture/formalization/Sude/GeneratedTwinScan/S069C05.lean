import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145358893 145391661 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 145358893 145391661).card = 97 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145358893 145391661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145391661 145424429 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 145391661 145424429).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145391661 145424429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145424429 145457197 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 145424429 145457197).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145424429 145457197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145457197 145489965 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 145457197 145489965).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145457197 145489965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 145358893 145424429).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 145358893 ≤ 145391661)
    (by decide : 145391661 ≤ 145424429) block0 block1

theorem join_0_1 : (twinPrimeSegment 145424429 145489965).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 145424429 ≤ 145457197)
    (by decide : 145457197 ≤ 145489965) block2 block3

theorem join_1_0 : (twinPrimeSegment 145358893 145489965).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 145358893 ≤ 145424429)
    (by decide : 145424429 ≤ 145489965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 145358893 145489965).card = 442 := join_1_0

end S069C05
end Sude.GeneratedTwinScan
