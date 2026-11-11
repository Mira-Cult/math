import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109838381 109871149 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 109838381 109871149).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109838381 109871149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109871149 109903917 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 109871149 109903917).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109871149 109903917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109903917 109936685 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 109903917 109936685).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109903917 109936685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109936685 109969453 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 109936685 109969453).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109936685 109969453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 109838381 109903917).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 109838381 ≤ 109871149)
    (by decide : 109871149 ≤ 109903917) block0 block1

theorem join_0_1 : (twinPrimeSegment 109903917 109969453).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 109903917 ≤ 109936685)
    (by decide : 109936685 ≤ 109969453) block2 block3

theorem join_1_0 : (twinPrimeSegment 109838381 109969453).card = 537 := by
  simpa using combineTwinPrimeSegments (by decide : 109838381 ≤ 109903917)
    (by decide : 109903917 ≤ 109969453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 109838381 109969453).card = 537 := join_1_0

end S052C06
end Sude.GeneratedTwinScan
