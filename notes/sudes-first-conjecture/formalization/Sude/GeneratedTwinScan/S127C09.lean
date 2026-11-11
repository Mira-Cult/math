import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S127C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16356)) 267517997 267550765 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 267517997 267550765).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16356 267517997 267550765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16357)) 267550765 267583533 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 267550765 267583533).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16357 267550765 267583533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16358)) 267583533 267616301 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 267583533 267616301).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16358 267583533 267616301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16359)) 267616301 267649069 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 267616301 267649069).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16359 267616301 267649069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 267517997 267583533).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 267517997 ≤ 267550765)
    (by decide : 267550765 ≤ 267583533) block0 block1

theorem join_0_1 : (twinPrimeSegment 267583533 267649069).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 267583533 ≤ 267616301)
    (by decide : 267616301 ≤ 267649069) block2 block3

theorem join_1_0 : (twinPrimeSegment 267517997 267649069).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 267517997 ≤ 267583533)
    (by decide : 267583533 ≤ 267649069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 267517997 267649069).card = 415 := join_1_0

end S127C09
end Sude.GeneratedTwinScan
