import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15518)) 240779309 240812077 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 240779309 240812077).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15518 240779309 240812077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15519)) 240812077 240844845 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 240812077 240844845).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15519 240812077 240844845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15520)) 240844845 240877613 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 240844845 240877613).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15520 240844845 240877613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15521)) 240877613 240910381 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 240877613 240910381).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15521 240877613 240910381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 240779309 240844845).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 240779309 ≤ 240812077)
    (by decide : 240812077 ≤ 240844845) block0 block1

theorem join_0_1 : (twinPrimeSegment 240844845 240910381).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 240844845 ≤ 240877613)
    (by decide : 240877613 ≤ 240910381) block2 block3

theorem join_1_0 : (twinPrimeSegment 240779309 240910381).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 240779309 ≤ 240844845)
    (by decide : 240844845 ≤ 240910381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 240779309 240910381).card = 452 := join_1_0

end S114C13
end Sude.GeneratedTwinScan
