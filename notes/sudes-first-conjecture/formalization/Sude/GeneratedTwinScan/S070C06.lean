import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147587117 147619885 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 147587117 147619885).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147587117 147619885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147619885 147652653 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 147619885 147652653).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147619885 147652653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147652653 147685421 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 147652653 147685421).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147652653 147685421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147685421 147718189 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 147685421 147718189).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147685421 147718189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 147587117 147652653).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 147587117 ≤ 147619885)
    (by decide : 147619885 ≤ 147652653) block0 block1

theorem join_0_1 : (twinPrimeSegment 147652653 147718189).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 147652653 ≤ 147685421)
    (by decide : 147685421 ≤ 147718189) block2 block3

theorem join_1_0 : (twinPrimeSegment 147587117 147718189).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 147587117 ≤ 147652653)
    (by decide : 147652653 ≤ 147718189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 147587117 147718189).card = 502 := join_1_0

end S070C06
end Sude.GeneratedTwinScan
