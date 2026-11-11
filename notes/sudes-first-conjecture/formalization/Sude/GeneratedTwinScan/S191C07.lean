import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20037)) 401473581 401506349 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 401473581 401506349).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20037 401473581 401506349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20038)) 401506349 401539117 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 401506349 401539117).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20038 401506349 401539117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20039)) 401539117 401571885 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 401539117 401571885).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20039 401539117 401571885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20040)) 401571885 401604653 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 401571885 401604653).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20040 401571885 401604653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 401473581 401539117).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 401473581 ≤ 401506349)
    (by decide : 401506349 ≤ 401539117) block0 block1

theorem join_0_1 : (twinPrimeSegment 401539117 401604653).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 401539117 ≤ 401571885)
    (by decide : 401571885 ≤ 401604653) block2 block3

theorem join_1_0 : (twinPrimeSegment 401473581 401604653).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 401473581 ≤ 401539117)
    (by decide : 401539117 ≤ 401604653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 401473581 401604653).card = 456 := join_1_0

end S191C07
end Sude.GeneratedTwinScan
