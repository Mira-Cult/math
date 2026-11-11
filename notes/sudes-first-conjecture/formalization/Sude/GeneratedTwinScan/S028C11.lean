import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60162093 60194861 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 60162093 60194861).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60162093 60194861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60194861 60227629 = 154 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 60194861 60227629).card = 154 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60194861 60227629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60227629 60260397 = 151 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 60227629 60260397).card = 151 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60227629 60260397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60260397 60293165 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 60260397 60293165).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60260397 60293165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 60162093 60227629).card = 295 := by
  simpa using combineTwinPrimeSegments (by decide : 60162093 ≤ 60194861)
    (by decide : 60194861 ≤ 60227629) block0 block1

theorem join_0_1 : (twinPrimeSegment 60227629 60293165).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 60227629 ≤ 60260397)
    (by decide : 60260397 ≤ 60293165) block2 block3

theorem join_1_0 : (twinPrimeSegment 60162093 60293165).card = 576 := by
  simpa using combineTwinPrimeSegments (by decide : 60162093 ≤ 60227629)
    (by decide : 60227629 ≤ 60293165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 60162093 60293165).card = 576 := join_1_0

end S028C11
end Sude.GeneratedTwinScan
