import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85327917 85360685 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 85327917 85360685).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85327917 85360685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85360685 85393453 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 85360685 85393453).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85360685 85393453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85393453 85426221 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 85393453 85426221).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85393453 85426221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85426221 85458989 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 85426221 85458989).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85426221 85458989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 85327917 85393453).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 85327917 ≤ 85360685)
    (by decide : 85360685 ≤ 85393453) block0 block1

theorem join_0_1 : (twinPrimeSegment 85393453 85458989).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 85393453 ≤ 85426221)
    (by decide : 85426221 ≤ 85458989) block2 block3

theorem join_1_0 : (twinPrimeSegment 85327917 85458989).card = 542 := by
  simpa using combineTwinPrimeSegments (by decide : 85327917 ≤ 85393453)
    (by decide : 85393453 ≤ 85458989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 85327917 85458989).card = 542 := join_1_0

end S040C11
end Sude.GeneratedTwinScan
