import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22412)) 502267949 502300717 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 502267949 502300717).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22412 502267949 502300717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22412)) 502300717 502333485 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 502300717 502333485).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22412 502300717 502333485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22413)) 502333485 502366253 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 502333485 502366253).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22413 502333485 502366253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22414)) 502366253 502399021 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 502366253 502399021).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22414 502366253 502399021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 502267949 502333485).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 502267949 ≤ 502300717)
    (by decide : 502300717 ≤ 502333485) block0 block1

theorem join_0_1 : (twinPrimeSegment 502333485 502399021).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 502333485 ≤ 502366253)
    (by decide : 502366253 ≤ 502399021) block2 block3

theorem join_1_0 : (twinPrimeSegment 502267949 502399021).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 502267949 ≤ 502333485)
    (by decide : 502333485 ≤ 502399021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 502267949 502399021).card = 418 := join_1_0

end S239C08
end Sude.GeneratedTwinScan
