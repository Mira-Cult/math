import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72351789 72384557 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 72351789 72384557).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72351789 72384557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72384557 72417325 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 72384557 72417325).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72384557 72417325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72417325 72450093 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 72417325 72450093).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72417325 72450093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72450093 72482861 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 72450093 72482861).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72450093 72482861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 72351789 72417325).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 72351789 ≤ 72384557)
    (by decide : 72384557 ≤ 72417325) block0 block1

theorem join_0_1 : (twinPrimeSegment 72417325 72482861).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 72417325 ≤ 72450093)
    (by decide : 72450093 ≤ 72482861) block2 block3

theorem join_1_0 : (twinPrimeSegment 72351789 72482861).card = 530 := by
  simpa using combineTwinPrimeSegments (by decide : 72351789 ≤ 72417325)
    (by decide : 72417325 ≤ 72482861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 72351789 72482861).card = 530 := join_1_0

end S034C08
end Sude.GeneratedTwinScan
