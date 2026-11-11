import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22447)) 503840813 503873581 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 503840813 503873581).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22447 503840813 503873581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22447)) 503873581 503906349 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 503873581 503906349).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22447 503873581 503906349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22448)) 503906349 503939117 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 503906349 503939117).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22448 503906349 503939117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22449)) 503939117 503971885 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 503939117 503971885).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22449 503939117 503971885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 503840813 503906349).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 503840813 ≤ 503873581)
    (by decide : 503873581 ≤ 503906349) block0 block1

theorem join_0_1 : (twinPrimeSegment 503906349 503971885).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 503906349 ≤ 503939117)
    (by decide : 503939117 ≤ 503971885) block2 block3

theorem join_1_0 : (twinPrimeSegment 503840813 503971885).card = 406 := by
  simpa using combineTwinPrimeSegments (by decide : 503840813 ≤ 503906349)
    (by decide : 503906349 ≤ 503971885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 503840813 503971885).card = 406 := join_1_0

end S240C04
end Sude.GeneratedTwinScan
