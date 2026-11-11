import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15752)) 248119341 248152109 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 248119341 248152109).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15752 248119341 248152109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15753)) 248152109 248184877 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 248152109 248184877).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15753 248152109 248184877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15754)) 248184877 248217645 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 248184877 248217645).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15754 248184877 248217645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15755)) 248217645 248250413 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 248217645 248250413).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15755 248217645 248250413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 248119341 248184877).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 248119341 ≤ 248152109)
    (by decide : 248152109 ≤ 248184877) block0 block1

theorem join_0_1 : (twinPrimeSegment 248184877 248250413).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 248184877 ≤ 248217645)
    (by decide : 248217645 ≤ 248250413) block2 block3

theorem join_1_0 : (twinPrimeSegment 248119341 248250413).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 248119341 ≤ 248184877)
    (by decide : 248184877 ≤ 248250413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 248119341 248250413).card = 456 := join_1_0

end S118C05
end Sude.GeneratedTwinScan
