import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22702)) 515375149 515407917 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 515375149 515407917).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22702 515375149 515407917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22703)) 515407917 515440685 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 515407917 515440685).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22703 515407917 515440685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22704)) 515440685 515473453 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 515440685 515473453).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22704 515440685 515473453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22704)) 515473453 515506221 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 515473453 515506221).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22704 515473453 515506221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 515375149 515440685).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 515375149 ≤ 515407917)
    (by decide : 515407917 ≤ 515440685) block0 block1

theorem join_0_1 : (twinPrimeSegment 515440685 515506221).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 515440685 ≤ 515473453)
    (by decide : 515473453 ≤ 515506221) block2 block3

theorem join_1_0 : (twinPrimeSegment 515375149 515506221).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 515375149 ≤ 515440685)
    (by decide : 515440685 ≤ 515506221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 515375149 515506221).card = 431 := join_1_0

end S245C12
end Sude.GeneratedTwinScan
