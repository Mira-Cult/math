import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21704)) 471072813 471105581 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 471072813 471105581).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21704 471072813 471105581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21705)) 471105581 471138349 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 471105581 471138349).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21705 471105581 471138349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21706)) 471138349 471171117 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 471138349 471171117).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21706 471138349 471171117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21707)) 471171117 471203885 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 471171117 471203885).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21707 471171117 471203885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 471072813 471138349).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 471072813 ≤ 471105581)
    (by decide : 471105581 ≤ 471138349) block0 block1

theorem join_0_1 : (twinPrimeSegment 471138349 471203885).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 471138349 ≤ 471171117)
    (by decide : 471171117 ≤ 471203885) block2 block3

theorem join_1_0 : (twinPrimeSegment 471072813 471203885).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 471072813 ≤ 471138349)
    (by decide : 471138349 ≤ 471203885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 471072813 471203885).card = 439 := join_1_0

end S224C10
end Sude.GeneratedTwinScan
