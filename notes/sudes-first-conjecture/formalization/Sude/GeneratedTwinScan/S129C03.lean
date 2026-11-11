import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16460)) 270925869 270958637 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 270925869 270958637).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16460 270925869 270958637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16461)) 270958637 270991405 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 270958637 270991405).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16461 270958637 270991405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16462)) 270991405 271024173 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 270991405 271024173).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16462 270991405 271024173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16463)) 271024173 271056941 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 271024173 271056941).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16463 271024173 271056941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 270925869 270991405).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 270925869 ≤ 270958637)
    (by decide : 270958637 ≤ 270991405) block0 block1

theorem join_0_1 : (twinPrimeSegment 270991405 271056941).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 270991405 ≤ 271024173)
    (by decide : 271024173 ≤ 271056941) block2 block3

theorem join_1_0 : (twinPrimeSegment 270925869 271056941).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 270925869 ≤ 270991405)
    (by decide : 270991405 ≤ 271056941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 270925869 271056941).card = 438 := join_1_0

end S129C03
end Sude.GeneratedTwinScan
