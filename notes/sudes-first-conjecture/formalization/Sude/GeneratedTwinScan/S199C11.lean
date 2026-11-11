import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20464)) 418775085 418807853 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 418775085 418807853).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20464 418775085 418807853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20465)) 418807853 418840621 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 418807853 418840621).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20465 418807853 418840621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20466)) 418840621 418873389 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 418840621 418873389).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20466 418840621 418873389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20467)) 418873389 418906157 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 418873389 418906157).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20467 418873389 418906157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 418775085 418840621).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 418775085 ≤ 418807853)
    (by decide : 418807853 ≤ 418840621) block0 block1

theorem join_0_1 : (twinPrimeSegment 418840621 418906157).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 418840621 ≤ 418873389)
    (by decide : 418873389 ≤ 418906157) block2 block3

theorem join_1_0 : (twinPrimeSegment 418775085 418906157).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 418775085 ≤ 418840621)
    (by decide : 418840621 ≤ 418906157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 418775085 418906157).card = 455 := join_1_0

end S199C11
end Sude.GeneratedTwinScan
