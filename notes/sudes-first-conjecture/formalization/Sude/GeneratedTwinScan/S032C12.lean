import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68681773 68714541 = 159 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 68681773 68714541).card = 159 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68681773 68714541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68714541 68747309 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 68714541 68747309).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68714541 68747309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68747309 68780077 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 68747309 68780077).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68747309 68780077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68780077 68812845 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 68780077 68812845).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68780077 68812845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 68681773 68747309).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 68681773 ≤ 68714541)
    (by decide : 68714541 ≤ 68747309) block0 block1

theorem join_0_1 : (twinPrimeSegment 68747309 68812845).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 68747309 ≤ 68780077)
    (by decide : 68780077 ≤ 68812845) block2 block3

theorem join_1_0 : (twinPrimeSegment 68681773 68812845).card = 543 := by
  simpa using combineTwinPrimeSegments (by decide : 68681773 ≤ 68747309)
    (by decide : 68747309 ≤ 68812845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 68681773 68812845).card = 543 := join_1_0

end S032C12
end Sude.GeneratedTwinScan
