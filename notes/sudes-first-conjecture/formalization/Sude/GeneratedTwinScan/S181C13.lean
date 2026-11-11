import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19527)) 381288493 381321261 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 381288493 381321261).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19527 381288493 381321261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19528)) 381321261 381354029 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 381321261 381354029).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19528 381321261 381354029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19529)) 381354029 381386797 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 381354029 381386797).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19529 381354029 381386797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19529)) 381386797 381419565 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 381386797 381419565).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19529 381386797 381419565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 381288493 381354029).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 381288493 ≤ 381321261)
    (by decide : 381321261 ≤ 381354029) block0 block1

theorem join_0_1 : (twinPrimeSegment 381354029 381419565).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 381354029 ≤ 381386797)
    (by decide : 381386797 ≤ 381419565) block2 block3

theorem join_1_0 : (twinPrimeSegment 381288493 381419565).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 381288493 ≤ 381354029)
    (by decide : 381354029 ≤ 381419565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 381288493 381419565).card = 467 := join_1_0

end S181C13
end Sude.GeneratedTwinScan
