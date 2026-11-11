import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21129)) 446431277 446464045 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 446431277 446464045).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21129 446431277 446464045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21130)) 446464045 446496813 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 446464045 446496813).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21130 446464045 446496813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21131)) 446496813 446529581 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 446496813 446529581).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21131 446496813 446529581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21132)) 446529581 446562349 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 446529581 446562349).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21132 446529581 446562349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 446431277 446496813).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 446431277 ≤ 446464045)
    (by decide : 446464045 ≤ 446496813) block0 block1

theorem join_0_1 : (twinPrimeSegment 446496813 446562349).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 446496813 ≤ 446529581)
    (by decide : 446529581 ≤ 446562349) block2 block3

theorem join_1_0 : (twinPrimeSegment 446431277 446562349).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 446431277 ≤ 446496813)
    (by decide : 446496813 ≤ 446562349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 446431277 446562349).card = 460 := join_1_0

end S212C14
end Sude.GeneratedTwinScan
