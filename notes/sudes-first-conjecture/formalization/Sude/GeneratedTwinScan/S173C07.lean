import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19072)) 363724845 363757613 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 363724845 363757613).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19072 363724845 363757613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19073)) 363757613 363790381 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 363757613 363790381).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19073 363757613 363790381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19074)) 363790381 363823149 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 363790381 363823149).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19074 363790381 363823149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19075)) 363823149 363855917 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 363823149 363855917).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19075 363823149 363855917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 363724845 363790381).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 363724845 ≤ 363757613)
    (by decide : 363757613 ≤ 363790381) block0 block1

theorem join_0_1 : (twinPrimeSegment 363790381 363855917).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 363790381 ≤ 363823149)
    (by decide : 363823149 ≤ 363855917) block2 block3

theorem join_1_0 : (twinPrimeSegment 363724845 363855917).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 363724845 ≤ 363790381)
    (by decide : 363790381 ≤ 363855917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 363724845 363855917).card = 440 := join_1_0

end S173C07
end Sude.GeneratedTwinScan
