import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20531)) 421527597 421560365 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 421527597 421560365).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20531 421527597 421560365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20532)) 421560365 421593133 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 421560365 421593133).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20532 421560365 421593133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20533)) 421593133 421625901 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 421593133 421625901).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20533 421593133 421625901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20534)) 421625901 421658669 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 421625901 421658669).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20534 421625901 421658669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 421527597 421593133).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 421527597 ≤ 421560365)
    (by decide : 421560365 ≤ 421593133) block0 block1

theorem join_0_1 : (twinPrimeSegment 421593133 421658669).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 421593133 ≤ 421625901)
    (by decide : 421625901 ≤ 421658669) block2 block3

theorem join_1_0 : (twinPrimeSegment 421527597 421658669).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 421527597 ≤ 421593133)
    (by decide : 421593133 ≤ 421658669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 421527597 421658669).card = 446 := join_1_0

end S201C00
end Sude.GeneratedTwinScan
