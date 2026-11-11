import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146800685 146833453 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 146800685 146833453).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146800685 146833453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146833453 146866221 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 146833453 146866221).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146833453 146866221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146866221 146898989 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 146866221 146898989).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146866221 146898989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146898989 146931757 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 146898989 146931757).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146898989 146931757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 146800685 146866221).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 146800685 ≤ 146833453)
    (by decide : 146833453 ≤ 146866221) block0 block1

theorem join_0_1 : (twinPrimeSegment 146866221 146931757).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 146866221 ≤ 146898989)
    (by decide : 146898989 ≤ 146931757) block2 block3

theorem join_1_0 : (twinPrimeSegment 146800685 146931757).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 146800685 ≤ 146866221)
    (by decide : 146866221 ≤ 146931757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 146800685 146931757).card = 506 := join_1_0

end S070C00
end Sude.GeneratedTwinScan
