import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14827)) 219807789 219840557 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 219807789 219840557).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14827 219807789 219840557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14828)) 219840557 219873325 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 219840557 219873325).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14828 219840557 219873325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14829)) 219873325 219906093 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 219873325 219906093).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14829 219873325 219906093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14830)) 219906093 219938861 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 219906093 219938861).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14830 219906093 219938861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 219807789 219873325).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 219807789 ≤ 219840557)
    (by decide : 219840557 ≤ 219873325) block0 block1

theorem join_0_1 : (twinPrimeSegment 219873325 219938861).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 219873325 ≤ 219906093)
    (by decide : 219906093 ≤ 219938861) block2 block3

theorem join_1_0 : (twinPrimeSegment 219807789 219938861).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 219807789 ≤ 219873325)
    (by decide : 219873325 ≤ 219938861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 219807789 219938861).card = 450 := join_1_0

end S104C13
end Sude.GeneratedTwinScan
