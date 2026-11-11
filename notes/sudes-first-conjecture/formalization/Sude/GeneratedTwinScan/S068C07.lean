import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143523885 143556653 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 143523885 143556653).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143523885 143556653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143556653 143589421 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 143556653 143589421).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143556653 143589421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143589421 143622189 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 143589421 143622189).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143589421 143622189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143622189 143654957 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 143622189 143654957).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143622189 143654957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 143523885 143589421).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 143523885 ≤ 143556653)
    (by decide : 143556653 ≤ 143589421) block0 block1

theorem join_0_1 : (twinPrimeSegment 143589421 143654957).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 143589421 ≤ 143622189)
    (by decide : 143622189 ≤ 143654957) block2 block3

theorem join_1_0 : (twinPrimeSegment 143523885 143654957).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 143523885 ≤ 143589421)
    (by decide : 143589421 ≤ 143654957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 143523885 143654957).card = 484 := join_1_0

end S068C07
end Sude.GeneratedTwinScan
