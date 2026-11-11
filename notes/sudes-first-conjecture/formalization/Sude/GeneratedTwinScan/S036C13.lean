import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77201453 77234221 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 77201453 77234221).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77201453 77234221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77234221 77266989 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 77234221 77266989).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77234221 77266989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77266989 77299757 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 77266989 77299757).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77266989 77299757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77299757 77332525 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 77299757 77332525).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77299757 77332525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 77201453 77266989).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 77201453 ≤ 77234221)
    (by decide : 77234221 ≤ 77266989) block0 block1

theorem join_0_1 : (twinPrimeSegment 77266989 77332525).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 77266989 ≤ 77299757)
    (by decide : 77299757 ≤ 77332525) block2 block3

theorem join_1_0 : (twinPrimeSegment 77201453 77332525).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 77201453 ≤ 77266989)
    (by decide : 77266989 ≤ 77332525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 77201453 77332525).card = 506 := join_1_0

end S036C13
end Sude.GeneratedTwinScan
