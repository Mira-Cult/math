import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13706)) 187826221 187858989 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 187826221 187858989).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13706 187826221 187858989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13707)) 187858989 187891757 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 187858989 187891757).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13707 187858989 187891757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13708)) 187891757 187924525 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 187891757 187924525).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13708 187891757 187924525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13709)) 187924525 187957293 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 187924525 187957293).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13709 187924525 187957293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 187826221 187891757).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 187826221 ≤ 187858989)
    (by decide : 187858989 ≤ 187891757) block0 block1

theorem join_0_1 : (twinPrimeSegment 187891757 187957293).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 187891757 ≤ 187924525)
    (by decide : 187924525 ≤ 187957293) block2 block3

theorem join_1_0 : (twinPrimeSegment 187826221 187957293).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 187826221 ≤ 187891757)
    (by decide : 187891757 ≤ 187957293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 187826221 187957293).card = 511 := join_1_0

end S089C09
end Sude.GeneratedTwinScan
