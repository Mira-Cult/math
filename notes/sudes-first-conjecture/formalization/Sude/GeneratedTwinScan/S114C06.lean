import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15488)) 239861805 239894573 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 239861805 239894573).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15488 239861805 239894573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15489)) 239894573 239927341 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 239894573 239927341).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15489 239894573 239927341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15490)) 239927341 239960109 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 239927341 239960109).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15490 239927341 239960109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15491)) 239960109 239992877 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 239960109 239992877).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15491 239960109 239992877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 239861805 239927341).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 239861805 ≤ 239894573)
    (by decide : 239894573 ≤ 239927341) block0 block1

theorem join_0_1 : (twinPrimeSegment 239927341 239992877).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 239927341 ≤ 239960109)
    (by decide : 239960109 ≤ 239992877) block2 block3

theorem join_1_0 : (twinPrimeSegment 239861805 239992877).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 239861805 ≤ 239927341)
    (by decide : 239927341 ≤ 239992877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 239861805 239992877).card = 488 := join_1_0

end S114C06
end Sude.GeneratedTwinScan
