import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13189)) 173932589 173965357 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 173932589 173965357).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13189 173932589 173965357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13190)) 173965357 173998125 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 173965357 173998125).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13190 173965357 173998125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13192)) 173998125 174030893 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 173998125 174030893).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13192 173998125 174030893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13193)) 174030893 174063661 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 174030893 174063661).card = 142 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13193 174030893 174063661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 173932589 173998125).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 173932589 ≤ 173965357)
    (by decide : 173965357 ≤ 173998125) block0 block1

theorem join_0_1 : (twinPrimeSegment 173998125 174063661).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 173998125 ≤ 174030893)
    (by decide : 174030893 ≤ 174063661) block2 block3

theorem join_1_0 : (twinPrimeSegment 173932589 174063661).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 173932589 ≤ 173998125)
    (by decide : 173998125 ≤ 174063661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 173932589 174063661).card = 497 := join_1_0

end S082C15
end Sude.GeneratedTwinScan
