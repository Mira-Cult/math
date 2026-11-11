import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16396)) 268828717 268861485 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 268828717 268861485).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16396 268828717 268861485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16397)) 268861485 268894253 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 268861485 268894253).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16397 268861485 268894253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16398)) 268894253 268927021 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 268894253 268927021).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16398 268894253 268927021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16399)) 268927021 268959789 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 268927021 268959789).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16399 268927021 268959789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 268828717 268894253).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 268828717 ≤ 268861485)
    (by decide : 268861485 ≤ 268894253) block0 block1

theorem join_0_1 : (twinPrimeSegment 268894253 268959789).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 268894253 ≤ 268927021)
    (by decide : 268927021 ≤ 268959789) block2 block3

theorem join_1_0 : (twinPrimeSegment 268828717 268959789).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 268828717 ≤ 268894253)
    (by decide : 268894253 ≤ 268959789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 268828717 268959789).card = 475 := join_1_0

end S128C03
end Sude.GeneratedTwinScan
