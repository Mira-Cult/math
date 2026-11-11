import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17902)) 320471085 320503853 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 320471085 320503853).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17902 320471085 320503853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17903)) 320503853 320536621 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 320503853 320536621).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17903 320503853 320536621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17904)) 320536621 320569389 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 320536621 320569389).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17904 320536621 320569389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17905)) 320569389 320602157 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 320569389 320602157).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17905 320569389 320602157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 320471085 320536621).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 320471085 ≤ 320503853)
    (by decide : 320503853 ≤ 320536621) block0 block1

theorem join_0_1 : (twinPrimeSegment 320536621 320602157).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 320536621 ≤ 320569389)
    (by decide : 320569389 ≤ 320602157) block2 block3

theorem join_1_0 : (twinPrimeSegment 320471085 320602157).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 320471085 ≤ 320536621)
    (by decide : 320536621 ≤ 320602157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 320471085 320602157).card = 432 := join_1_0

end S152C13
end Sude.GeneratedTwinScan
