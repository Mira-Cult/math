import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22789)) 519307309 519340077 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 519307309 519340077).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22789 519307309 519340077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22789)) 519340077 519372845 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 519340077 519372845).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22789 519340077 519372845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22790)) 519372845 519405613 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 519372845 519405613).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22790 519372845 519405613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22791)) 519405613 519438381 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 519405613 519438381).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22791 519405613 519438381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 519307309 519372845).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 519307309 ≤ 519340077)
    (by decide : 519340077 ≤ 519372845) block0 block1

theorem join_0_1 : (twinPrimeSegment 519372845 519438381).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 519372845 ≤ 519405613)
    (by decide : 519405613 ≤ 519438381) block2 block3

theorem join_1_0 : (twinPrimeSegment 519307309 519438381).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 519307309 ≤ 519372845)
    (by decide : 519372845 ≤ 519438381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 519307309 519438381).card = 425 := join_1_0

end S247C10
end Sude.GeneratedTwinScan
