import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17238)) 297140269 297173037 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 297140269 297173037).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17238 297140269 297173037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17239)) 297173037 297205805 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 297173037 297205805).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17239 297173037 297205805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17240)) 297205805 297238573 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 297205805 297238573).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17240 297205805 297238573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17241)) 297238573 297271341 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 297238573 297271341).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17241 297238573 297271341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 297140269 297205805).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 297140269 ≤ 297173037)
    (by decide : 297173037 ≤ 297205805) block0 block1

theorem join_0_1 : (twinPrimeSegment 297205805 297271341).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 297205805 ≤ 297238573)
    (by decide : 297238573 ≤ 297271341) block2 block3

theorem join_1_0 : (twinPrimeSegment 297140269 297271341).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 297140269 ≤ 297205805)
    (by decide : 297205805 ≤ 297271341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 297140269 297271341).card = 478 := join_1_0

end S141C11
end Sude.GeneratedTwinScan
