import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18792)) 353108013 353140781 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 353108013 353140781).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18792 353108013 353140781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18792)) 353140781 353173549 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 353140781 353173549).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18792 353140781 353173549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18793)) 353173549 353206317 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 353173549 353206317).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18793 353173549 353206317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18794)) 353206317 353239085 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 353206317 353239085).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18794 353206317 353239085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 353108013 353173549).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 353108013 ≤ 353140781)
    (by decide : 353140781 ≤ 353173549) block0 block1

theorem join_0_1 : (twinPrimeSegment 353173549 353239085).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 353173549 ≤ 353206317)
    (by decide : 353206317 ≤ 353239085) block2 block3

theorem join_1_0 : (twinPrimeSegment 353108013 353239085).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 353108013 ≤ 353173549)
    (by decide : 353173549 ≤ 353239085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 353108013 353239085).card = 434 := join_1_0

end S168C06
end Sude.GeneratedTwinScan
