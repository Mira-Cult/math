import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22832)) 521273389 521306157 = 91 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 521273389 521306157).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22832 521273389 521306157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22832)) 521306157 521338925 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 521306157 521338925).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22832 521306157 521338925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22833)) 521338925 521371693 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 521338925 521371693).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22833 521338925 521371693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22834)) 521371693 521404461 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 521371693 521404461).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22834 521371693 521404461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 521273389 521338925).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 521273389 ≤ 521306157)
    (by decide : 521306157 ≤ 521338925) block0 block1

theorem join_0_1 : (twinPrimeSegment 521338925 521404461).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 521338925 ≤ 521371693)
    (by decide : 521371693 ≤ 521404461) block2 block3

theorem join_1_0 : (twinPrimeSegment 521273389 521404461).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 521273389 ≤ 521338925)
    (by decide : 521338925 ≤ 521404461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 521273389 521404461).card = 425 := join_1_0

end S248C09
end Sude.GeneratedTwinScan
