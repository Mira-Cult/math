import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146538541 146571309 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 146538541 146571309).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146538541 146571309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146571309 146604077 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 146571309 146604077).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146571309 146604077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146604077 146636845 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 146604077 146636845).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146604077 146636845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146636845 146669613 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 146636845 146669613).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146636845 146669613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 146538541 146604077).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 146538541 ≤ 146571309)
    (by decide : 146571309 ≤ 146604077) block0 block1

theorem join_0_1 : (twinPrimeSegment 146604077 146669613).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 146604077 ≤ 146636845)
    (by decide : 146636845 ≤ 146669613) block2 block3

theorem join_1_0 : (twinPrimeSegment 146538541 146669613).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 146538541 ≤ 146604077)
    (by decide : 146604077 ≤ 146669613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 146538541 146669613).card = 490 := join_1_0

end S069C14
end Sude.GeneratedTwinScan
