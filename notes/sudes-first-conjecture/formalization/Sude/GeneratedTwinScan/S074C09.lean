import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12506)) 156368941 156401709 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 156368941 156401709).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12506 156368941 156401709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12507)) 156401709 156434477 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 156401709 156434477).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12507 156401709 156434477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12508)) 156434477 156467245 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 156434477 156467245).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12508 156434477 156467245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12509)) 156467245 156500013 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 156467245 156500013).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12509 156467245 156500013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 156368941 156434477).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 156368941 ≤ 156401709)
    (by decide : 156401709 ≤ 156434477) block0 block1

theorem join_0_1 : (twinPrimeSegment 156434477 156500013).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 156434477 ≤ 156467245)
    (by decide : 156467245 ≤ 156500013) block2 block3

theorem join_1_0 : (twinPrimeSegment 156368941 156500013).card = 505 := by
  simpa using combineTwinPrimeSegments (by decide : 156368941 ≤ 156434477)
    (by decide : 156434477 ≤ 156500013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 156368941 156500013).card = 505 := join_1_0

end S074C09
end Sude.GeneratedTwinScan
