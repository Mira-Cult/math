import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12416)) 154140717 154173485 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 154140717 154173485).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12416 154140717 154173485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12417)) 154173485 154206253 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 154173485 154206253).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12417 154173485 154206253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12419)) 154206253 154239021 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 154206253 154239021).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12419 154206253 154239021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12420)) 154239021 154271789 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 154239021 154271789).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12420 154239021 154271789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 154140717 154206253).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 154140717 ≤ 154173485)
    (by decide : 154173485 ≤ 154206253) block0 block1

theorem join_0_1 : (twinPrimeSegment 154206253 154271789).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 154206253 ≤ 154239021)
    (by decide : 154239021 ≤ 154271789) block2 block3

theorem join_1_0 : (twinPrimeSegment 154140717 154271789).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 154140717 ≤ 154206253)
    (by decide : 154206253 ≤ 154271789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 154140717 154271789).card = 471 := join_1_0

end S073C08
end Sude.GeneratedTwinScan
