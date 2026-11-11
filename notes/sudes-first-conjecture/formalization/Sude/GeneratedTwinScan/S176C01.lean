import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19216)) 369229869 369262637 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 369229869 369262637).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19216 369229869 369262637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19217)) 369262637 369295405 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 369262637 369295405).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19217 369262637 369295405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19217)) 369295405 369328173 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 369295405 369328173).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19217 369295405 369328173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19218)) 369328173 369360941 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 369328173 369360941).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19218 369328173 369360941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 369229869 369295405).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 369229869 ≤ 369262637)
    (by decide : 369262637 ≤ 369295405) block0 block1

theorem join_0_1 : (twinPrimeSegment 369295405 369360941).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 369295405 ≤ 369328173)
    (by decide : 369328173 ≤ 369360941) block2 block3

theorem join_1_0 : (twinPrimeSegment 369229869 369360941).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 369229869 ≤ 369295405)
    (by decide : 369295405 ≤ 369360941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 369229869 369360941).card = 460 := join_1_0

end S176C01
end Sude.GeneratedTwinScan
