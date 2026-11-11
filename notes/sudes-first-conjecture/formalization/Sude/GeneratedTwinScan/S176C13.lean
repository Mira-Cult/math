import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19257)) 370802733 370835501 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 370802733 370835501).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19257 370802733 370835501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19257)) 370835501 370868269 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 370835501 370868269).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19257 370835501 370868269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19258)) 370868269 370901037 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 370868269 370901037).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19258 370868269 370901037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19259)) 370901037 370933805 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 370901037 370933805).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19259 370901037 370933805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 370802733 370868269).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 370802733 ≤ 370835501)
    (by decide : 370835501 ≤ 370868269) block0 block1

theorem join_0_1 : (twinPrimeSegment 370868269 370933805).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 370868269 ≤ 370901037)
    (by decide : 370901037 ≤ 370933805) block2 block3

theorem join_1_0 : (twinPrimeSegment 370802733 370933805).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 370802733 ≤ 370868269)
    (by decide : 370868269 ≤ 370933805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 370802733 370933805).card = 451 := join_1_0

end S176C13
end Sude.GeneratedTwinScan
