import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21771)) 473956397 473989165 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 473956397 473989165).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21771 473956397 473989165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21772)) 473989165 474021933 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 473989165 474021933).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21772 473989165 474021933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21772)) 474021933 474054701 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 474021933 474054701).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21772 474021933 474054701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21773)) 474054701 474087469 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 474054701 474087469).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21773 474054701 474087469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 473956397 474021933).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 473956397 ≤ 473989165)
    (by decide : 473989165 ≤ 474021933) block0 block1

theorem join_0_1 : (twinPrimeSegment 474021933 474087469).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 474021933 ≤ 474054701)
    (by decide : 474054701 ≤ 474087469) block2 block3

theorem join_1_0 : (twinPrimeSegment 473956397 474087469).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 473956397 ≤ 474021933)
    (by decide : 474021933 ≤ 474087469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 473956397 474087469).card = 439 := join_1_0

end S226C00
end Sude.GeneratedTwinScan
