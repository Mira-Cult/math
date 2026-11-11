import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72482861 72515629 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 72482861 72515629).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72482861 72515629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72515629 72548397 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 72515629 72548397).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72515629 72548397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72548397 72581165 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 72548397 72581165).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72548397 72581165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72581165 72613933 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 72581165 72613933).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72581165 72613933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 72482861 72548397).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 72482861 ≤ 72515629)
    (by decide : 72515629 ≤ 72548397) block0 block1

theorem join_0_1 : (twinPrimeSegment 72548397 72613933).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 72548397 ≤ 72581165)
    (by decide : 72581165 ≤ 72613933) block2 block3

theorem join_1_0 : (twinPrimeSegment 72482861 72613933).card = 541 := by
  simpa using combineTwinPrimeSegments (by decide : 72482861 ≤ 72548397)
    (by decide : 72548397 ≤ 72613933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 72482861 72613933).card = 541 := join_1_0

end S034C09
end Sude.GeneratedTwinScan
