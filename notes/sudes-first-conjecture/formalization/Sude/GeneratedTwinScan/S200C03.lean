import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20490)) 419823661 419856429 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 419823661 419856429).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20490 419823661 419856429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20491)) 419856429 419889197 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 419856429 419889197).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20491 419856429 419889197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20491)) 419889197 419921965 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 419889197 419921965).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20491 419889197 419921965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20492)) 419921965 419954733 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 419921965 419954733).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20492 419921965 419954733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 419823661 419889197).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 419823661 ≤ 419856429)
    (by decide : 419856429 ≤ 419889197) block0 block1

theorem join_0_1 : (twinPrimeSegment 419889197 419954733).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 419889197 ≤ 419921965)
    (by decide : 419921965 ≤ 419954733) block2 block3

theorem join_1_0 : (twinPrimeSegment 419823661 419954733).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 419823661 ≤ 419889197)
    (by decide : 419889197 ≤ 419954733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 419823661 419954733).card = 470 := join_1_0

end S200C03
end Sude.GeneratedTwinScan
