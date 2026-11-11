import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19500)) 380239917 380272685 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 380239917 380272685).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19500 380239917 380272685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19501)) 380272685 380305453 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 380272685 380305453).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19501 380272685 380305453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19502)) 380305453 380338221 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 380305453 380338221).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19502 380305453 380338221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19503)) 380338221 380370989 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 380338221 380370989).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19503 380338221 380370989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 380239917 380305453).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 380239917 ≤ 380272685)
    (by decide : 380272685 ≤ 380305453) block0 block1

theorem join_0_1 : (twinPrimeSegment 380305453 380370989).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 380305453 ≤ 380338221)
    (by decide : 380338221 ≤ 380370989) block2 block3

theorem join_1_0 : (twinPrimeSegment 380239917 380370989).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 380239917 ≤ 380305453)
    (by decide : 380305453 ≤ 380370989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 380239917 380370989).card = 450 := join_1_0

end S181C05
end Sude.GeneratedTwinScan
