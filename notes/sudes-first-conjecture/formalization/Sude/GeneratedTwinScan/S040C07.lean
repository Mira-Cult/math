import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84803629 84836397 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 84803629 84836397).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84803629 84836397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84836397 84869165 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 84836397 84869165).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84836397 84869165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84869165 84901933 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 84869165 84901933).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84869165 84901933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84901933 84934701 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 84901933 84934701).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84901933 84934701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 84803629 84869165).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 84803629 ≤ 84836397)
    (by decide : 84836397 ≤ 84869165) block0 block1

theorem join_0_1 : (twinPrimeSegment 84869165 84934701).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 84869165 ≤ 84901933)
    (by decide : 84901933 ≤ 84934701) block2 block3

theorem join_1_0 : (twinPrimeSegment 84803629 84934701).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 84803629 ≤ 84869165)
    (by decide : 84869165 ≤ 84934701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 84803629 84934701).card = 489 := join_1_0

end S040C07
end Sude.GeneratedTwinScan
