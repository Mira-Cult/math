import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22426)) 502923309 502956077 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 502923309 502956077).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22426 502923309 502956077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22427)) 502956077 502988845 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 502956077 502988845).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22427 502956077 502988845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22428)) 502988845 503021613 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 502988845 503021613).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22428 502988845 503021613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22428)) 503021613 503054381 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 503021613 503054381).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22428 503021613 503054381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 502923309 502988845).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 502923309 ≤ 502956077)
    (by decide : 502956077 ≤ 502988845) block0 block1

theorem join_0_1 : (twinPrimeSegment 502988845 503054381).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 502988845 ≤ 503021613)
    (by decide : 503021613 ≤ 503054381) block2 block3

theorem join_1_0 : (twinPrimeSegment 502923309 503054381).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 502923309 ≤ 502988845)
    (by decide : 502988845 ≤ 503054381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 502923309 503054381).card = 454 := join_1_0

end S239C13
end Sude.GeneratedTwinScan
