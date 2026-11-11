import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13049)) 170262573 170295341 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 170262573 170295341).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13049 170262573 170295341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13050)) 170295341 170328109 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 170295341 170328109).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13050 170295341 170328109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13052)) 170328109 170360877 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 170328109 170360877).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13052 170328109 170360877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13053)) 170360877 170393645 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 170360877 170393645).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13053 170360877 170393645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 170262573 170328109).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 170262573 ≤ 170295341)
    (by decide : 170295341 ≤ 170328109) block0 block1

theorem join_0_1 : (twinPrimeSegment 170328109 170393645).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 170328109 ≤ 170360877)
    (by decide : 170360877 ≤ 170393645) block2 block3

theorem join_1_0 : (twinPrimeSegment 170262573 170393645).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 170262573 ≤ 170328109)
    (by decide : 170328109 ≤ 170393645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 170262573 170393645).card = 482 := join_1_0

end S081C03
end Sude.GeneratedTwinScan
