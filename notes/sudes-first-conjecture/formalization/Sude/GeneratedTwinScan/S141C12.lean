import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17242)) 297271341 297304109 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 297271341 297304109).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17242 297271341 297304109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17243)) 297304109 297336877 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 297304109 297336877).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17243 297304109 297336877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17244)) 297336877 297369645 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 297336877 297369645).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17244 297336877 297369645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17245)) 297369645 297402413 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 297369645 297402413).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17245 297369645 297402413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 297271341 297336877).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 297271341 ≤ 297304109)
    (by decide : 297304109 ≤ 297336877) block0 block1

theorem join_0_1 : (twinPrimeSegment 297336877 297402413).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 297336877 ≤ 297369645)
    (by decide : 297369645 ≤ 297402413) block2 block3

theorem join_1_0 : (twinPrimeSegment 297271341 297402413).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 297271341 ≤ 297336877)
    (by decide : 297336877 ≤ 297402413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 297271341 297402413).card = 455 := join_1_0

end S141C12
end Sude.GeneratedTwinScan
