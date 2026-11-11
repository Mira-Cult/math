import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14822)) 219676717 219709485 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 219676717 219709485).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14822 219676717 219709485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14823)) 219709485 219742253 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 219709485 219742253).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14823 219709485 219742253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14824)) 219742253 219775021 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 219742253 219775021).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14824 219742253 219775021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14825)) 219775021 219807789 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 219775021 219807789).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14825 219775021 219807789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 219676717 219742253).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 219676717 ≤ 219709485)
    (by decide : 219709485 ≤ 219742253) block0 block1

theorem join_0_1 : (twinPrimeSegment 219742253 219807789).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 219742253 ≤ 219775021)
    (by decide : 219775021 ≤ 219807789) block2 block3

theorem join_1_0 : (twinPrimeSegment 219676717 219807789).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 219676717 ≤ 219742253)
    (by decide : 219742253 ≤ 219807789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 219676717 219807789).card = 488 := join_1_0

end S104C12
end Sude.GeneratedTwinScan
