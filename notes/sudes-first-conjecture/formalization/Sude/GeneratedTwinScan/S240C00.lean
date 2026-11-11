import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22435)) 503316525 503349293 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 503316525 503349293).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22435 503316525 503349293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22436)) 503349293 503382061 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 503349293 503382061).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22436 503349293 503382061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22436)) 503382061 503414829 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 503382061 503414829).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22436 503382061 503414829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22437)) 503414829 503447597 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 503414829 503447597).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22437 503414829 503447597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 503316525 503382061).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 503316525 ≤ 503349293)
    (by decide : 503349293 ≤ 503382061) block0 block1

theorem join_0_1 : (twinPrimeSegment 503382061 503447597).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 503382061 ≤ 503414829)
    (by decide : 503414829 ≤ 503447597) block2 block3

theorem join_1_0 : (twinPrimeSegment 503316525 503447597).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 503316525 ≤ 503382061)
    (by decide : 503382061 ≤ 503447597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 503316525 503447597).card = 428 := join_1_0

end S240C00
end Sude.GeneratedTwinScan
