import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20223)) 408944685 408977453 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 408944685 408977453).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20223 408944685 408977453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20224)) 408977453 409010221 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 408977453 409010221).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20224 408977453 409010221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20224)) 409010221 409042989 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 409010221 409042989).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20224 409010221 409042989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20225)) 409042989 409075757 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 409042989 409075757).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20225 409042989 409075757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 408944685 409010221).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 408944685 ≤ 408977453)
    (by decide : 408977453 ≤ 409010221) block0 block1

theorem join_0_1 : (twinPrimeSegment 409010221 409075757).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 409010221 ≤ 409042989)
    (by decide : 409042989 ≤ 409075757) block2 block3

theorem join_1_0 : (twinPrimeSegment 408944685 409075757).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 408944685 ≤ 409010221)
    (by decide : 409010221 ≤ 409075757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 408944685 409075757).card = 448 := join_1_0

end S195C00
end Sude.GeneratedTwinScan
