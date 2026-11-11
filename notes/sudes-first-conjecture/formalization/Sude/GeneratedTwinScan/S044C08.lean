import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S044C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93323309 93356077 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 93323309 93356077).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93323309 93356077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93356077 93388845 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 93356077 93388845).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93356077 93388845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93388845 93421613 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 93388845 93421613).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93388845 93421613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93421613 93454381 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 93421613 93454381).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93421613 93454381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 93323309 93388845).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 93323309 ≤ 93356077)
    (by decide : 93356077 ≤ 93388845) block0 block1

theorem join_0_1 : (twinPrimeSegment 93388845 93454381).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 93388845 ≤ 93421613)
    (by decide : 93421613 ≤ 93454381) block2 block3

theorem join_1_0 : (twinPrimeSegment 93323309 93454381).card = 525 := by
  simpa using combineTwinPrimeSegments (by decide : 93323309 ≤ 93388845)
    (by decide : 93388845 ≤ 93454381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 93323309 93454381).card = 525 := join_1_0

end S044C08
end Sude.GeneratedTwinScan
