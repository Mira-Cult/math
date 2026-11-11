import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19038)) 362414125 362446893 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 362414125 362446893).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19038 362414125 362446893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19038)) 362446893 362479661 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 362446893 362479661).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19038 362446893 362479661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19039)) 362479661 362512429 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 362479661 362512429).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19039 362479661 362512429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19040)) 362512429 362545197 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 362512429 362545197).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19040 362512429 362545197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 362414125 362479661).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 362414125 ≤ 362446893)
    (by decide : 362446893 ≤ 362479661) block0 block1

theorem join_0_1 : (twinPrimeSegment 362479661 362545197).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 362479661 ≤ 362512429)
    (by decide : 362512429 ≤ 362545197) block2 block3

theorem join_1_0 : (twinPrimeSegment 362414125 362545197).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 362414125 ≤ 362479661)
    (by decide : 362479661 ≤ 362545197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 362414125 362545197).card = 441 := join_1_0

end S172C13
end Sude.GeneratedTwinScan
