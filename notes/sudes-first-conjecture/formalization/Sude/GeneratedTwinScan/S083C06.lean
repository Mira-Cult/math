import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13224)) 174850093 174882861 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 174850093 174882861).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13224 174850093 174882861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13225)) 174882861 174915629 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 174882861 174915629).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13225 174882861 174915629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13226)) 174915629 174948397 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 174915629 174948397).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13226 174915629 174948397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13228)) 174948397 174981165 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 174948397 174981165).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13228 174948397 174981165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 174850093 174915629).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 174850093 ≤ 174882861)
    (by decide : 174882861 ≤ 174915629) block0 block1

theorem join_0_1 : (twinPrimeSegment 174915629 174981165).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 174915629 ≤ 174948397)
    (by decide : 174948397 ≤ 174981165) block2 block3

theorem join_1_0 : (twinPrimeSegment 174850093 174981165).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 174850093 ≤ 174915629)
    (by decide : 174915629 ≤ 174981165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 174850093 174981165).card = 486 := join_1_0

end S083C06
end Sude.GeneratedTwinScan
