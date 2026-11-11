import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16827)) 283115565 283148333 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 283115565 283148333).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16827 283115565 283148333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16827)) 283148333 283181101 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 283148333 283181101).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16827 283148333 283181101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16828)) 283181101 283213869 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 283181101 283213869).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16828 283181101 283213869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16829)) 283213869 283246637 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 283213869 283246637).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16829 283213869 283246637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 283115565 283181101).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 283115565 ≤ 283148333)
    (by decide : 283148333 ≤ 283181101) block0 block1

theorem join_0_1 : (twinPrimeSegment 283181101 283246637).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 283181101 ≤ 283213869)
    (by decide : 283213869 ≤ 283246637) block2 block3

theorem join_1_0 : (twinPrimeSegment 283115565 283246637).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 283115565 ≤ 283181101)
    (by decide : 283181101 ≤ 283246637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 283115565 283246637).card = 464 := join_1_0

end S135C00
end Sude.GeneratedTwinScan
