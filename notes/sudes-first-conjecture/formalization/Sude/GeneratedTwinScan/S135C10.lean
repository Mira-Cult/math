import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16865)) 284426285 284459053 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 284426285 284459053).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16865 284426285 284459053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16866)) 284459053 284491821 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 284459053 284491821).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16866 284459053 284491821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16867)) 284491821 284524589 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 284491821 284524589).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16867 284491821 284524589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16868)) 284524589 284557357 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 284524589 284557357).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16868 284524589 284557357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 284426285 284491821).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 284426285 ≤ 284459053)
    (by decide : 284459053 ≤ 284491821) block0 block1

theorem join_0_1 : (twinPrimeSegment 284491821 284557357).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 284491821 ≤ 284524589)
    (by decide : 284524589 ≤ 284557357) block2 block3

theorem join_1_0 : (twinPrimeSegment 284426285 284557357).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 284426285 ≤ 284491821)
    (by decide : 284491821 ≤ 284557357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 284426285 284557357).card = 434 := join_1_0

end S135C10
end Sude.GeneratedTwinScan
