import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14092)) 198574125 198606893 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 198574125 198606893).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14092 198574125 198606893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14093)) 198606893 198639661 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 198606893 198639661).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14093 198606893 198639661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14095)) 198639661 198672429 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 198639661 198672429).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14095 198639661 198672429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14096)) 198672429 198705197 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 198672429 198705197).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14096 198672429 198705197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 198574125 198639661).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 198574125 ≤ 198606893)
    (by decide : 198606893 ≤ 198639661) block0 block1

theorem join_0_1 : (twinPrimeSegment 198639661 198705197).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 198639661 ≤ 198672429)
    (by decide : 198672429 ≤ 198705197) block2 block3

theorem join_1_0 : (twinPrimeSegment 198574125 198705197).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 198574125 ≤ 198639661)
    (by decide : 198639661 ≤ 198705197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 198574125 198705197).card = 467 := join_1_0

end S094C11
end Sude.GeneratedTwinScan
