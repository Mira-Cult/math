import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19607)) 384434221 384466989 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 384434221 384466989).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19607 384434221 384466989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19608)) 384466989 384499757 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 384466989 384499757).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19608 384466989 384499757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19609)) 384499757 384532525 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 384499757 384532525).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19609 384499757 384532525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19610)) 384532525 384565293 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 384532525 384565293).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19610 384532525 384565293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 384434221 384499757).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 384434221 ≤ 384466989)
    (by decide : 384466989 ≤ 384499757) block0 block1

theorem join_0_1 : (twinPrimeSegment 384499757 384565293).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 384499757 ≤ 384532525)
    (by decide : 384532525 ≤ 384565293) block2 block3

theorem join_1_0 : (twinPrimeSegment 384434221 384565293).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 384434221 ≤ 384499757)
    (by decide : 384499757 ≤ 384565293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 384434221 384565293).card = 421 := join_1_0

end S183C05
end Sude.GeneratedTwinScan
