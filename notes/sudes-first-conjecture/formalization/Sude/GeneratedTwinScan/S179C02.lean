import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19382)) 375652397 375685165 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 375652397 375685165).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19382 375652397 375685165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19383)) 375685165 375717933 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 375685165 375717933).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19383 375685165 375717933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19384)) 375717933 375750701 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 375717933 375750701).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19384 375717933 375750701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19385)) 375750701 375783469 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 375750701 375783469).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19385 375750701 375783469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 375652397 375717933).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 375652397 ≤ 375685165)
    (by decide : 375685165 ≤ 375717933) block0 block1

theorem join_0_1 : (twinPrimeSegment 375717933 375783469).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 375717933 ≤ 375750701)
    (by decide : 375750701 ≤ 375783469) block2 block3

theorem join_1_0 : (twinPrimeSegment 375652397 375783469).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 375652397 ≤ 375717933)
    (by decide : 375717933 ≤ 375783469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 375652397 375783469).card = 429 := join_1_0

end S179C02
end Sude.GeneratedTwinScan
