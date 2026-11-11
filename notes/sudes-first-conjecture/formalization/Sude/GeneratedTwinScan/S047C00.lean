import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98566189 98598957 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 98566189 98598957).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98566189 98598957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98598957 98631725 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 98598957 98631725).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98598957 98631725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98631725 98664493 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 98631725 98664493).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98631725 98664493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98664493 98697261 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 98664493 98697261).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98664493 98697261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 98566189 98631725).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 98566189 ≤ 98598957)
    (by decide : 98598957 ≤ 98631725) block0 block1

theorem join_0_1 : (twinPrimeSegment 98631725 98697261).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 98631725 ≤ 98664493)
    (by decide : 98664493 ≤ 98697261) block2 block3

theorem join_1_0 : (twinPrimeSegment 98566189 98697261).card = 523 := by
  simpa using combineTwinPrimeSegments (by decide : 98566189 ≤ 98631725)
    (by decide : 98631725 ≤ 98697261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 98566189 98697261).card = 523 := join_1_0

end S047C00
end Sude.GeneratedTwinScan
