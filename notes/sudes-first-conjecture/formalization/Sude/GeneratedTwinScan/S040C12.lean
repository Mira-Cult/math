import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85458989 85491757 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 85458989 85491757).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85458989 85491757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85491757 85524525 = 152 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 85491757 85524525).card = 152 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85491757 85524525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85524525 85557293 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 85524525 85557293).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85524525 85557293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85557293 85590061 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 85557293 85590061).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85557293 85590061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 85458989 85524525).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 85458989 ≤ 85491757)
    (by decide : 85491757 ≤ 85524525) block0 block1

theorem join_0_1 : (twinPrimeSegment 85524525 85590061).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 85524525 ≤ 85557293)
    (by decide : 85557293 ≤ 85590061) block2 block3

theorem join_1_0 : (twinPrimeSegment 85458989 85590061).card = 544 := by
  simpa using combineTwinPrimeSegments (by decide : 85458989 ≤ 85524525)
    (by decide : 85524525 ≤ 85590061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 85458989 85590061).card = 544 := join_1_0

end S040C12
end Sude.GeneratedTwinScan
