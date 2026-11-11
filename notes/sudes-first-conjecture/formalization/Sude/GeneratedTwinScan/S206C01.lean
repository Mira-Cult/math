import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20788)) 432144429 432177197 = 90 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 432144429 432177197).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20788 432144429 432177197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20789)) 432177197 432209965 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 432177197 432209965).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20789 432177197 432209965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20790)) 432209965 432242733 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 432209965 432242733).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20790 432209965 432242733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20791)) 432242733 432275501 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 432242733 432275501).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20791 432242733 432275501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 432144429 432209965).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 432144429 ≤ 432177197)
    (by decide : 432177197 ≤ 432209965) block0 block1

theorem join_0_1 : (twinPrimeSegment 432209965 432275501).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 432209965 ≤ 432242733)
    (by decide : 432242733 ≤ 432275501) block2 block3

theorem join_1_0 : (twinPrimeSegment 432144429 432275501).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 432144429 ≤ 432209965)
    (by decide : 432209965 ≤ 432275501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 432144429 432275501).card = 428 := join_1_0

end S206C01
end Sude.GeneratedTwinScan
