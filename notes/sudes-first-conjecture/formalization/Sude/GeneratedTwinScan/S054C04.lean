import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113770541 113803309 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 113770541 113803309).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113770541 113803309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113803309 113836077 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 113803309 113836077).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113803309 113836077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113836077 113868845 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 113836077 113868845).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113836077 113868845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113868845 113901613 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 113868845 113901613).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113868845 113901613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 113770541 113836077).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 113770541 ≤ 113803309)
    (by decide : 113803309 ≤ 113836077) block0 block1

theorem join_0_1 : (twinPrimeSegment 113836077 113901613).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 113836077 ≤ 113868845)
    (by decide : 113868845 ≤ 113901613) block2 block3

theorem join_1_0 : (twinPrimeSegment 113770541 113901613).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 113770541 ≤ 113836077)
    (by decide : 113836077 ≤ 113901613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 113770541 113901613).card = 494 := join_1_0

end S054C04
end Sude.GeneratedTwinScan
