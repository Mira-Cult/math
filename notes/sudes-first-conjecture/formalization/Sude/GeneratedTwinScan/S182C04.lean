import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19550)) 382205997 382238765 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 382205997 382238765).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19550 382205997 382238765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19551)) 382238765 382271533 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 382238765 382271533).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19551 382238765 382271533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19552)) 382271533 382304301 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 382271533 382304301).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19552 382271533 382304301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19553)) 382304301 382337069 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 382304301 382337069).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19553 382304301 382337069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 382205997 382271533).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 382205997 ≤ 382238765)
    (by decide : 382238765 ≤ 382271533) block0 block1

theorem join_0_1 : (twinPrimeSegment 382271533 382337069).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 382271533 ≤ 382304301)
    (by decide : 382304301 ≤ 382337069) block2 block3

theorem join_1_0 : (twinPrimeSegment 382205997 382337069).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 382205997 ≤ 382271533)
    (by decide : 382271533 ≤ 382337069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 382205997 382337069).card = 456 := join_1_0

end S182C04
end Sude.GeneratedTwinScan
