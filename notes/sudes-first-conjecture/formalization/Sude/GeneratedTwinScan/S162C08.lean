import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18461)) 340787245 340820013 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 340787245 340820013).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18461 340787245 340820013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18462)) 340820013 340852781 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 340820013 340852781).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18462 340820013 340852781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18463)) 340852781 340885549 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 340852781 340885549).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18463 340852781 340885549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18463)) 340885549 340918317 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 340885549 340918317).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18463 340885549 340918317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 340787245 340852781).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 340787245 ≤ 340820013)
    (by decide : 340820013 ≤ 340852781) block0 block1

theorem join_0_1 : (twinPrimeSegment 340852781 340918317).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 340852781 ≤ 340885549)
    (by decide : 340885549 ≤ 340918317) block2 block3

theorem join_1_0 : (twinPrimeSegment 340787245 340918317).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 340787245 ≤ 340852781)
    (by decide : 340852781 ≤ 340918317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 340787245 340918317).card = 447 := join_1_0

end S162C08
end Sude.GeneratedTwinScan
