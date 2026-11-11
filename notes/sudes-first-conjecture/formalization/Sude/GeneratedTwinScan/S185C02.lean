import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19704)) 388235309 388268077 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 388235309 388268077).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19704 388235309 388268077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19705)) 388268077 388300845 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 388268077 388300845).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19705 388268077 388300845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19706)) 388300845 388333613 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 388300845 388333613).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19706 388300845 388333613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19707)) 388333613 388366381 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 388333613 388366381).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19707 388333613 388366381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 388235309 388300845).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 388235309 ≤ 388268077)
    (by decide : 388268077 ≤ 388300845) block0 block1

theorem join_0_1 : (twinPrimeSegment 388300845 388366381).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 388300845 ≤ 388333613)
    (by decide : 388333613 ≤ 388366381) block2 block3

theorem join_1_0 : (twinPrimeSegment 388235309 388366381).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 388235309 ≤ 388300845)
    (by decide : 388300845 ≤ 388366381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 388235309 388366381).card = 455 := join_1_0

end S185C02
end Sude.GeneratedTwinScan
