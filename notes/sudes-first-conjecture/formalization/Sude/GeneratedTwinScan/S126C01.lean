import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16260)) 264372269 264405037 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 264372269 264405037).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16260 264372269 264405037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16261)) 264405037 264437805 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 264405037 264437805).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16261 264405037 264437805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16262)) 264437805 264470573 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 264437805 264470573).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16262 264437805 264470573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16263)) 264470573 264503341 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 264470573 264503341).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16263 264470573 264503341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 264372269 264437805).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 264372269 ≤ 264405037)
    (by decide : 264405037 ≤ 264437805) block0 block1

theorem join_0_1 : (twinPrimeSegment 264437805 264503341).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 264437805 ≤ 264470573)
    (by decide : 264470573 ≤ 264503341) block2 block3

theorem join_1_0 : (twinPrimeSegment 264372269 264503341).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 264372269 ≤ 264437805)
    (by decide : 264437805 ≤ 264503341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 264372269 264503341).card = 461 := join_1_0

end S126C01
end Sude.GeneratedTwinScan
