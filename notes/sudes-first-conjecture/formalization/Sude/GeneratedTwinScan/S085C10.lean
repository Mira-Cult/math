import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13401)) 179568685 179601453 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 179568685 179601453).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13401 179568685 179601453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13402)) 179601453 179634221 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 179601453 179634221).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13402 179601453 179634221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13403)) 179634221 179666989 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 179634221 179666989).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13403 179634221 179666989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13405)) 179666989 179699757 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 179666989 179699757).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13405 179666989 179699757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 179568685 179634221).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 179568685 ≤ 179601453)
    (by decide : 179601453 ≤ 179634221) block0 block1

theorem join_0_1 : (twinPrimeSegment 179634221 179699757).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 179634221 ≤ 179666989)
    (by decide : 179666989 ≤ 179699757) block2 block3

theorem join_1_0 : (twinPrimeSegment 179568685 179699757).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 179568685 ≤ 179634221)
    (by decide : 179634221 ≤ 179699757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 179568685 179699757).card = 497 := join_1_0

end S085C10
end Sude.GeneratedTwinScan
