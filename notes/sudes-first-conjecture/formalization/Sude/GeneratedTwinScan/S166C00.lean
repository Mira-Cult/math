import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18659)) 348127277 348160045 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 348127277 348160045).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18659 348127277 348160045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18659)) 348160045 348192813 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 348160045 348192813).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18659 348160045 348192813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18660)) 348192813 348225581 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 348192813 348225581).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18660 348192813 348225581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18661)) 348225581 348258349 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 348225581 348258349).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18661 348225581 348258349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 348127277 348192813).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 348127277 ≤ 348160045)
    (by decide : 348160045 ≤ 348192813) block0 block1

theorem join_0_1 : (twinPrimeSegment 348192813 348258349).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 348192813 ≤ 348225581)
    (by decide : 348225581 ≤ 348258349) block2 block3

theorem join_1_0 : (twinPrimeSegment 348127277 348258349).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 348127277 ≤ 348192813)
    (by decide : 348192813 ≤ 348258349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 348127277 348258349).card = 441 := join_1_0

end S166C00
end Sude.GeneratedTwinScan
