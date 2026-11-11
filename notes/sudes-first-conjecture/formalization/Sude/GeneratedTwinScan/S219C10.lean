import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21462)) 460587053 460619821 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 460587053 460619821).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21462 460587053 460619821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21462)) 460619821 460652589 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 460619821 460652589).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21462 460619821 460652589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21463)) 460652589 460685357 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 460652589 460685357).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21463 460652589 460685357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21464)) 460685357 460718125 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 460685357 460718125).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21464 460685357 460718125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 460587053 460652589).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 460587053 ≤ 460619821)
    (by decide : 460619821 ≤ 460652589) block0 block1

theorem join_0_1 : (twinPrimeSegment 460652589 460718125).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 460652589 ≤ 460685357)
    (by decide : 460685357 ≤ 460718125) block2 block3

theorem join_1_0 : (twinPrimeSegment 460587053 460718125).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 460587053 ≤ 460652589)
    (by decide : 460652589 ≤ 460718125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 460587053 460718125).card = 431 := join_1_0

end S219C10
end Sude.GeneratedTwinScan
