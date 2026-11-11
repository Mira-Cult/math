import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17898)) 320340013 320372781 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 320340013 320372781).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17898 320340013 320372781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17899)) 320372781 320405549 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 320372781 320405549).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17899 320372781 320405549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17900)) 320405549 320438317 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 320405549 320438317).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17900 320405549 320438317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17901)) 320438317 320471085 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 320438317 320471085).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17901 320438317 320471085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 320340013 320405549).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 320340013 ≤ 320372781)
    (by decide : 320372781 ≤ 320405549) block0 block1

theorem join_0_1 : (twinPrimeSegment 320405549 320471085).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 320405549 ≤ 320438317)
    (by decide : 320438317 ≤ 320471085) block2 block3

theorem join_1_0 : (twinPrimeSegment 320340013 320471085).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 320340013 ≤ 320405549)
    (by decide : 320405549 ≤ 320471085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 320340013 320471085).card = 446 := join_1_0

end S152C12
end Sude.GeneratedTwinScan
