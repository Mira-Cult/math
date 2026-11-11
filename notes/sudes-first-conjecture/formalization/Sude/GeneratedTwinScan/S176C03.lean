import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19223)) 369492013 369524781 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 369492013 369524781).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19223 369492013 369524781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19223)) 369524781 369557549 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 369524781 369557549).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19223 369524781 369557549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19224)) 369557549 369590317 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 369557549 369590317).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19224 369557549 369590317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19225)) 369590317 369623085 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 369590317 369623085).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19225 369590317 369623085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 369492013 369557549).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 369492013 ≤ 369524781)
    (by decide : 369524781 ≤ 369557549) block0 block1

theorem join_0_1 : (twinPrimeSegment 369557549 369623085).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 369557549 ≤ 369590317)
    (by decide : 369590317 ≤ 369623085) block2 block3

theorem join_1_0 : (twinPrimeSegment 369492013 369623085).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 369492013 ≤ 369557549)
    (by decide : 369557549 ≤ 369623085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 369492013 369623085).card = 415 := join_1_0

end S176C03
end Sude.GeneratedTwinScan
