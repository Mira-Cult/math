import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75628589 75661357 = 152 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 75628589 75661357).card = 152 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75628589 75661357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75661357 75694125 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 75661357 75694125).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75661357 75694125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75694125 75726893 = 148 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 75694125 75726893).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75694125 75726893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75726893 75759661 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 75726893 75759661).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75726893 75759661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 75628589 75694125).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 75628589 ≤ 75661357)
    (by decide : 75661357 ≤ 75694125) block0 block1

theorem join_0_1 : (twinPrimeSegment 75694125 75759661).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 75694125 ≤ 75726893)
    (by decide : 75726893 ≤ 75759661) block2 block3

theorem join_1_0 : (twinPrimeSegment 75628589 75759661).card = 561 := by
  simpa using combineTwinPrimeSegments (by decide : 75628589 ≤ 75694125)
    (by decide : 75694125 ≤ 75759661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 75628589 75759661).card = 561 := join_1_0

end S036C01
end Sude.GeneratedTwinScan
