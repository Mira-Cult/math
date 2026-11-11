import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114819117 114851885 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 114819117 114851885).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114819117 114851885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114851885 114884653 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 114851885 114884653).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114851885 114884653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114884653 114917421 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 114884653 114917421).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114884653 114917421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114917421 114950189 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 114917421 114950189).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114917421 114950189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 114819117 114884653).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 114819117 ≤ 114851885)
    (by decide : 114851885 ≤ 114884653) block0 block1

theorem join_0_1 : (twinPrimeSegment 114884653 114950189).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 114884653 ≤ 114917421)
    (by decide : 114917421 ≤ 114950189) block2 block3

theorem join_1_0 : (twinPrimeSegment 114819117 114950189).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 114819117 ≤ 114884653)
    (by decide : 114884653 ≤ 114950189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 114819117 114950189).card = 495 := join_1_0

end S054C12
end Sude.GeneratedTwinScan
