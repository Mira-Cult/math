import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19284)) 371851309 371884077 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 371851309 371884077).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19284 371851309 371884077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19285)) 371884077 371916845 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 371884077 371916845).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19285 371884077 371916845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19285)) 371916845 371949613 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 371916845 371949613).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19285 371916845 371949613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19286)) 371949613 371982381 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 371949613 371982381).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19286 371949613 371982381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 371851309 371916845).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 371851309 ≤ 371884077)
    (by decide : 371884077 ≤ 371916845) block0 block1

theorem join_0_1 : (twinPrimeSegment 371916845 371982381).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 371916845 ≤ 371949613)
    (by decide : 371949613 ≤ 371982381) block2 block3

theorem join_1_0 : (twinPrimeSegment 371851309 371982381).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 371851309 ≤ 371916845)
    (by decide : 371916845 ≤ 371982381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 371851309 371982381).card = 480 := join_1_0

end S177C05
end Sude.GeneratedTwinScan
