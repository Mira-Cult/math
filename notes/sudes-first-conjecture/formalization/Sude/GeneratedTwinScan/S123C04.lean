import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16078)) 258474029 258506797 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 258474029 258506797).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16078 258474029 258506797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16079)) 258506797 258539565 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 258506797 258539565).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16079 258506797 258539565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16080)) 258539565 258572333 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 258539565 258572333).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16080 258539565 258572333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16081)) 258572333 258605101 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 258572333 258605101).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16081 258572333 258605101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 258474029 258539565).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 258474029 ≤ 258506797)
    (by decide : 258506797 ≤ 258539565) block0 block1

theorem join_0_1 : (twinPrimeSegment 258539565 258605101).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 258539565 ≤ 258572333)
    (by decide : 258572333 ≤ 258605101) block2 block3

theorem join_1_0 : (twinPrimeSegment 258474029 258605101).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 258474029 ≤ 258539565)
    (by decide : 258539565 ≤ 258605101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 258474029 258605101).card = 460 := join_1_0

end S123C04
end Sude.GeneratedTwinScan
