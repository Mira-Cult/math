import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22511)) 506724397 506757165 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 506724397 506757165).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22511 506724397 506757165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22511)) 506757165 506789933 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 506757165 506789933).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22511 506757165 506789933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22512)) 506789933 506822701 = 89 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 506789933 506822701).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22512 506789933 506822701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22513)) 506822701 506855469 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 506822701 506855469).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22513 506822701 506855469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 506724397 506789933).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 506724397 ≤ 506757165)
    (by decide : 506757165 ≤ 506789933) block0 block1

theorem join_0_1 : (twinPrimeSegment 506789933 506855469).card = 183 := by
  simpa using combineTwinPrimeSegments (by decide : 506789933 ≤ 506822701)
    (by decide : 506822701 ≤ 506855469) block2 block3

theorem join_1_0 : (twinPrimeSegment 506724397 506855469).card = 409 := by
  simpa using combineTwinPrimeSegments (by decide : 506724397 ≤ 506789933)
    (by decide : 506789933 ≤ 506855469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 506724397 506855469).card = 409 := join_1_0

end S241C10
end Sude.GeneratedTwinScan
