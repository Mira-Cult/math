import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17517)) 306839597 306872365 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 306839597 306872365).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17517 306839597 306872365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17518)) 306872365 306905133 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 306872365 306905133).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17518 306872365 306905133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17519)) 306905133 306937901 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 306905133 306937901).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17519 306905133 306937901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17520)) 306937901 306970669 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 306937901 306970669).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17520 306937901 306970669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 306839597 306905133).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 306839597 ≤ 306872365)
    (by decide : 306872365 ≤ 306905133) block0 block1

theorem join_0_1 : (twinPrimeSegment 306905133 306970669).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 306905133 ≤ 306937901)
    (by decide : 306937901 ≤ 306970669) block2 block3

theorem join_1_0 : (twinPrimeSegment 306839597 306970669).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 306839597 ≤ 306905133)
    (by decide : 306905133 ≤ 306970669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 306839597 306970669).card = 476 := join_1_0

end S146C05
end Sude.GeneratedTwinScan
