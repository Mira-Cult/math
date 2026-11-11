import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130154541 130187309 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 130154541 130187309).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130154541 130187309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130187309 130220077 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 130187309 130220077).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130187309 130220077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130220077 130252845 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 130220077 130252845).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130220077 130252845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130252845 130285613 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 130252845 130285613).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130252845 130285613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 130154541 130220077).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 130154541 ≤ 130187309)
    (by decide : 130187309 ≤ 130220077) block0 block1

theorem join_0_1 : (twinPrimeSegment 130220077 130285613).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 130220077 ≤ 130252845)
    (by decide : 130252845 ≤ 130285613) block2 block3

theorem join_1_0 : (twinPrimeSegment 130154541 130285613).card = 521 := by
  simpa using combineTwinPrimeSegments (by decide : 130154541 ≤ 130220077)
    (by decide : 130220077 ≤ 130285613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 130154541 130285613).card = 521 := join_1_0

end S062C01
end Sude.GeneratedTwinScan
