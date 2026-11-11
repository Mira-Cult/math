import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12734)) 162136109 162168877 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 162136109 162168877).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12734 162136109 162168877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12735)) 162168877 162201645 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 162168877 162201645).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12735 162168877 162201645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12737)) 162201645 162234413 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 162201645 162234413).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12737 162201645 162234413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12738)) 162234413 162267181 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 162234413 162267181).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12738 162234413 162267181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 162136109 162201645).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 162136109 ≤ 162168877)
    (by decide : 162168877 ≤ 162201645) block0 block1

theorem join_0_1 : (twinPrimeSegment 162201645 162267181).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 162201645 ≤ 162234413)
    (by decide : 162234413 ≤ 162267181) block2 block3

theorem join_1_0 : (twinPrimeSegment 162136109 162267181).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 162136109 ≤ 162201645)
    (by decide : 162201645 ≤ 162267181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 162136109 162267181).card = 447 := join_1_0

end S077C05
end Sude.GeneratedTwinScan
