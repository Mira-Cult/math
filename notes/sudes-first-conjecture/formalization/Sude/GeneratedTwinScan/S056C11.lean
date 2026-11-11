import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118882349 118915117 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 118882349 118915117).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118882349 118915117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118915117 118947885 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 118915117 118947885).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118915117 118947885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118947885 118980653 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 118947885 118980653).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118947885 118980653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118980653 119013421 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 118980653 119013421).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118980653 119013421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 118882349 118947885).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 118882349 ≤ 118915117)
    (by decide : 118915117 ≤ 118947885) block0 block1

theorem join_0_1 : (twinPrimeSegment 118947885 119013421).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 118947885 ≤ 118980653)
    (by decide : 118980653 ≤ 119013421) block2 block3

theorem join_1_0 : (twinPrimeSegment 118882349 119013421).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 118882349 ≤ 118947885)
    (by decide : 118947885 ≤ 119013421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 118882349 119013421).card = 493 := join_1_0

end S056C11
end Sude.GeneratedTwinScan
