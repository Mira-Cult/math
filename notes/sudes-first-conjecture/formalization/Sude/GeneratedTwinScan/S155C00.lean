import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18030)) 325058605 325091373 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 325058605 325091373).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18030 325058605 325091373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18031)) 325091373 325124141 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 325091373 325124141).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18031 325091373 325124141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18032)) 325124141 325156909 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 325124141 325156909).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18032 325124141 325156909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18033)) 325156909 325189677 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 325156909 325189677).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18033 325156909 325189677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 325058605 325124141).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 325058605 ≤ 325091373)
    (by decide : 325091373 ≤ 325124141) block0 block1

theorem join_0_1 : (twinPrimeSegment 325124141 325189677).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 325124141 ≤ 325156909)
    (by decide : 325156909 ≤ 325189677) block2 block3

theorem join_1_0 : (twinPrimeSegment 325058605 325189677).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 325058605 ≤ 325124141)
    (by decide : 325124141 ≤ 325189677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 325058605 325189677).card = 454 := join_1_0

end S155C00
end Sude.GeneratedTwinScan
