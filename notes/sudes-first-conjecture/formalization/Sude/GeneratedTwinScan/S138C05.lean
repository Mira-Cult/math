import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17032)) 290062381 290095149 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 290062381 290095149).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17032 290062381 290095149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17033)) 290095149 290127917 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 290095149 290127917).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17033 290095149 290127917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17034)) 290127917 290160685 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 290127917 290160685).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17034 290127917 290160685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17035)) 290160685 290193453 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 290160685 290193453).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17035 290160685 290193453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 290062381 290127917).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 290062381 ≤ 290095149)
    (by decide : 290095149 ≤ 290127917) block0 block1

theorem join_0_1 : (twinPrimeSegment 290127917 290193453).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 290127917 ≤ 290160685)
    (by decide : 290160685 ≤ 290193453) block2 block3

theorem join_1_0 : (twinPrimeSegment 290062381 290193453).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 290062381 ≤ 290127917)
    (by decide : 290127917 ≤ 290193453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 290062381 290193453).card = 467 := join_1_0

end S138C05
end Sude.GeneratedTwinScan
