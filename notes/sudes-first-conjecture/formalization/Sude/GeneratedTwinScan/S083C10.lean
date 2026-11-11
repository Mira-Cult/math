import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13244)) 175374381 175407149 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 175374381 175407149).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13244 175374381 175407149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13245)) 175407149 175439917 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 175407149 175439917).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13245 175407149 175439917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13246)) 175439917 175472685 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 175439917 175472685).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13246 175439917 175472685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13247)) 175472685 175505453 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 175472685 175505453).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13247 175472685 175505453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 175374381 175439917).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 175374381 ≤ 175407149)
    (by decide : 175407149 ≤ 175439917) block0 block1

theorem join_0_1 : (twinPrimeSegment 175439917 175505453).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 175439917 ≤ 175472685)
    (by decide : 175472685 ≤ 175505453) block2 block3

theorem join_1_0 : (twinPrimeSegment 175374381 175505453).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 175374381 ≤ 175439917)
    (by decide : 175439917 ≤ 175505453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 175374381 175505453).card = 470 := join_1_0

end S083C10
end Sude.GeneratedTwinScan
