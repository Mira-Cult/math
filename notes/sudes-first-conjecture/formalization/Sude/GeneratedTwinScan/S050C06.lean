import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105644077 105676845 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 105644077 105676845).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105644077 105676845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105676845 105709613 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 105676845 105709613).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105676845 105709613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105709613 105742381 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 105709613 105742381).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105709613 105742381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105742381 105775149 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 105742381 105775149).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105742381 105775149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 105644077 105709613).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 105644077 ≤ 105676845)
    (by decide : 105676845 ≤ 105709613) block0 block1

theorem join_0_1 : (twinPrimeSegment 105709613 105775149).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 105709613 ≤ 105742381)
    (by decide : 105742381 ≤ 105775149) block2 block3

theorem join_1_0 : (twinPrimeSegment 105644077 105775149).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 105644077 ≤ 105709613)
    (by decide : 105709613 ≤ 105775149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 105644077 105775149).card = 480 := join_1_0

end S050C06
end Sude.GeneratedTwinScan
