import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18268)) 333709357 333742125 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 333709357 333742125).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18268 333709357 333742125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18269)) 333742125 333774893 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 333742125 333774893).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18269 333742125 333774893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18270)) 333774893 333807661 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 333774893 333807661).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18270 333774893 333807661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18271)) 333807661 333840429 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 333807661 333840429).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18271 333807661 333840429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 333709357 333774893).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 333709357 ≤ 333742125)
    (by decide : 333742125 ≤ 333774893) block0 block1

theorem join_0_1 : (twinPrimeSegment 333774893 333840429).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 333774893 ≤ 333807661)
    (by decide : 333807661 ≤ 333840429) block2 block3

theorem join_1_0 : (twinPrimeSegment 333709357 333840429).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 333709357 ≤ 333774893)
    (by decide : 333774893 ≤ 333840429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 333709357 333840429).card = 479 := join_1_0

end S159C02
end Sude.GeneratedTwinScan
