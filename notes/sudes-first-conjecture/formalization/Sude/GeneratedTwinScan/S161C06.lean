import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18397)) 338427949 338460717 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 338427949 338460717).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18397 338427949 338460717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18398)) 338460717 338493485 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 338460717 338493485).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18398 338460717 338493485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18399)) 338493485 338526253 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 338493485 338526253).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18399 338493485 338526253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18399)) 338526253 338559021 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 338526253 338559021).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18399 338526253 338559021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 338427949 338493485).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 338427949 ≤ 338460717)
    (by decide : 338460717 ≤ 338493485) block0 block1

theorem join_0_1 : (twinPrimeSegment 338493485 338559021).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 338493485 ≤ 338526253)
    (by decide : 338526253 ≤ 338559021) block2 block3

theorem join_1_0 : (twinPrimeSegment 338427949 338559021).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 338427949 ≤ 338493485)
    (by decide : 338493485 ≤ 338559021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 338427949 338559021).card = 451 := join_1_0

end S161C06
end Sude.GeneratedTwinScan
