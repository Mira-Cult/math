import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18297)) 334757933 334790701 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 334757933 334790701).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18297 334757933 334790701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18298)) 334790701 334823469 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 334790701 334823469).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18298 334790701 334823469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18299)) 334823469 334856237 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 334823469 334856237).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18299 334823469 334856237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18299)) 334856237 334889005 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 334856237 334889005).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18299 334856237 334889005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 334757933 334823469).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 334757933 ≤ 334790701)
    (by decide : 334790701 ≤ 334823469) block0 block1

theorem join_0_1 : (twinPrimeSegment 334823469 334889005).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 334823469 ≤ 334856237)
    (by decide : 334856237 ≤ 334889005) block2 block3

theorem join_1_0 : (twinPrimeSegment 334757933 334889005).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 334757933 ≤ 334823469)
    (by decide : 334823469 ≤ 334889005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 334757933 334889005).card = 436 := join_1_0

end S159C10
end Sude.GeneratedTwinScan
