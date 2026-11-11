import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22417)) 502530093 502562861 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 502530093 502562861).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22417 502530093 502562861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22418)) 502562861 502595629 = 86 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 502562861 502595629).card = 86 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22418 502562861 502595629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22419)) 502595629 502628397 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 502595629 502628397).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22419 502595629 502628397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22420)) 502628397 502661165 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 502628397 502661165).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22420 502628397 502661165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 502530093 502595629).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 502530093 ≤ 502562861)
    (by decide : 502562861 ≤ 502595629) block0 block1

theorem join_0_1 : (twinPrimeSegment 502595629 502661165).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 502595629 ≤ 502628397)
    (by decide : 502628397 ≤ 502661165) block2 block3

theorem join_1_0 : (twinPrimeSegment 502530093 502661165).card = 404 := by
  simpa using combineTwinPrimeSegments (by decide : 502530093 ≤ 502595629)
    (by decide : 502595629 ≤ 502661165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 502530093 502661165).card = 404 := join_1_0

end S239C10
end Sude.GeneratedTwinScan
