import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S180C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19460)) 378667053 378699821 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 378667053 378699821).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19460 378667053 378699821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19461)) 378699821 378732589 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 378699821 378732589).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19461 378699821 378732589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19461)) 378732589 378765357 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 378732589 378765357).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19461 378732589 378765357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19462)) 378765357 378798125 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 378765357 378798125).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19462 378765357 378798125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 378667053 378732589).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 378667053 ≤ 378699821)
    (by decide : 378699821 ≤ 378732589) block0 block1

theorem join_0_1 : (twinPrimeSegment 378732589 378798125).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 378732589 ≤ 378765357)
    (by decide : 378765357 ≤ 378798125) block2 block3

theorem join_1_0 : (twinPrimeSegment 378667053 378798125).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 378667053 ≤ 378732589)
    (by decide : 378732589 ≤ 378798125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 378667053 378798125).card = 436 := join_1_0

end S180C09
end Sude.GeneratedTwinScan
