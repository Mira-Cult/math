import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18486)) 341704749 341737517 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 341704749 341737517).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18486 341704749 341737517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18487)) 341737517 341770285 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 341737517 341770285).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18487 341737517 341770285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18487)) 341770285 341803053 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 341770285 341803053).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18487 341770285 341803053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18488)) 341803053 341835821 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 341803053 341835821).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18488 341803053 341835821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 341704749 341770285).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 341704749 ≤ 341737517)
    (by decide : 341737517 ≤ 341770285) block0 block1

theorem join_0_1 : (twinPrimeSegment 341770285 341835821).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 341770285 ≤ 341803053)
    (by decide : 341803053 ≤ 341835821) block2 block3

theorem join_1_0 : (twinPrimeSegment 341704749 341835821).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 341704749 ≤ 341770285)
    (by decide : 341770285 ≤ 341835821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 341704749 341835821).card = 430 := join_1_0

end S162C15
end Sude.GeneratedTwinScan
