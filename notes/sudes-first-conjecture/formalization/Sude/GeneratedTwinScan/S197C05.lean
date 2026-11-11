import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S197C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20342)) 413794349 413827117 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 413794349 413827117).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20342 413794349 413827117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20343)) 413827117 413859885 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 413827117 413859885).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20343 413827117 413859885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20344)) 413859885 413892653 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 413859885 413892653).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20344 413859885 413892653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20345)) 413892653 413925421 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 413892653 413925421).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20345 413892653 413925421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 413794349 413859885).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 413794349 ≤ 413827117)
    (by decide : 413827117 ≤ 413859885) block0 block1

theorem join_0_1 : (twinPrimeSegment 413859885 413925421).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 413859885 ≤ 413892653)
    (by decide : 413892653 ≤ 413925421) block2 block3

theorem join_1_0 : (twinPrimeSegment 413794349 413925421).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 413794349 ≤ 413859885)
    (by decide : 413859885 ≤ 413925421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 413794349 413925421).card = 435 := join_1_0

end S197C05
end Sude.GeneratedTwinScan
