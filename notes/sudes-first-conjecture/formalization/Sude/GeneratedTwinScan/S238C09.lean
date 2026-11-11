import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22368)) 500301869 500334637 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 500301869 500334637).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22368 500301869 500334637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22368)) 500334637 500367405 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 500334637 500367405).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22368 500334637 500367405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22369)) 500367405 500400173 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 500367405 500400173).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22369 500367405 500400173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22370)) 500400173 500432941 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 500400173 500432941).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22370 500400173 500432941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 500301869 500367405).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 500301869 ≤ 500334637)
    (by decide : 500334637 ≤ 500367405) block0 block1

theorem join_0_1 : (twinPrimeSegment 500367405 500432941).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 500367405 ≤ 500400173)
    (by decide : 500400173 ≤ 500432941) block2 block3

theorem join_1_0 : (twinPrimeSegment 500301869 500432941).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 500301869 ≤ 500367405)
    (by decide : 500367405 ≤ 500432941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 500301869 500432941).card = 439 := join_1_0

end S238C09
end Sude.GeneratedTwinScan
