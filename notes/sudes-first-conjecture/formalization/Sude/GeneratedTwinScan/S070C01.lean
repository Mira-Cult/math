import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146931757 146964525 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 146931757 146964525).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146931757 146964525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146964525 146997293 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 146964525 146997293).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146964525 146997293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146997293 147030061 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 146997293 147030061).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146997293 147030061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147030061 147062829 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 147030061 147062829).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147030061 147062829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 146931757 146997293).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 146931757 ≤ 146964525)
    (by decide : 146964525 ≤ 146997293) block0 block1

theorem join_0_1 : (twinPrimeSegment 146997293 147062829).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 146997293 ≤ 147030061)
    (by decide : 147030061 ≤ 147062829) block2 block3

theorem join_1_0 : (twinPrimeSegment 146931757 147062829).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 146931757 ≤ 146997293)
    (by decide : 146997293 ≤ 147062829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 146931757 147062829).card = 508 := join_1_0

end S070C01
end Sude.GeneratedTwinScan
