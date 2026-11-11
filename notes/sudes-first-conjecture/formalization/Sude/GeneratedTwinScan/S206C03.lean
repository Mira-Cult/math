import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20795)) 432406573 432439341 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 432406573 432439341).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20795 432406573 432439341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20795)) 432439341 432472109 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 432439341 432472109).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20795 432439341 432472109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20796)) 432472109 432504877 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 432472109 432504877).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20796 432472109 432504877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20797)) 432504877 432537645 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 432504877 432537645).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20797 432504877 432537645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 432406573 432472109).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 432406573 ≤ 432439341)
    (by decide : 432439341 ≤ 432472109) block0 block1

theorem join_0_1 : (twinPrimeSegment 432472109 432537645).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 432472109 ≤ 432504877)
    (by decide : 432504877 ≤ 432537645) block2 block3

theorem join_1_0 : (twinPrimeSegment 432406573 432537645).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 432406573 ≤ 432472109)
    (by decide : 432472109 ≤ 432537645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 432406573 432537645).card = 425 := join_1_0

end S206C03
end Sude.GeneratedTwinScan
