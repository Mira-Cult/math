import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131203117 131235885 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 131203117 131235885).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131203117 131235885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131235885 131268653 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 131235885 131268653).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131235885 131268653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131268653 131301421 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 131268653 131301421).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131268653 131301421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131301421 131334189 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 131301421 131334189).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131301421 131334189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 131203117 131268653).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 131203117 ≤ 131235885)
    (by decide : 131235885 ≤ 131268653) block0 block1

theorem join_0_1 : (twinPrimeSegment 131268653 131334189).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 131268653 ≤ 131301421)
    (by decide : 131301421 ≤ 131334189) block2 block3

theorem join_1_0 : (twinPrimeSegment 131203117 131334189).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 131203117 ≤ 131268653)
    (by decide : 131268653 ≤ 131334189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 131203117 131334189).card = 470 := join_1_0

end S062C09
end Sude.GeneratedTwinScan
