import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16567)) 274464813 274497581 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 274464813 274497581).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16567 274464813 274497581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16568)) 274497581 274530349 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 274497581 274530349).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16568 274497581 274530349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16569)) 274530349 274563117 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 274530349 274563117).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16569 274530349 274563117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16570)) 274563117 274595885 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 274563117 274595885).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16570 274563117 274595885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 274464813 274530349).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 274464813 ≤ 274497581)
    (by decide : 274497581 ≤ 274530349) block0 block1

theorem join_0_1 : (twinPrimeSegment 274530349 274595885).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 274530349 ≤ 274563117)
    (by decide : 274563117 ≤ 274595885) block2 block3

theorem join_1_0 : (twinPrimeSegment 274464813 274595885).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 274464813 ≤ 274530349)
    (by decide : 274530349 ≤ 274595885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 274464813 274595885).card = 432 := join_1_0

end S130C14
end Sude.GeneratedTwinScan
