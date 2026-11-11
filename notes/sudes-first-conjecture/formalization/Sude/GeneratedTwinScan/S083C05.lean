import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13219)) 174719021 174751789 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 174719021 174751789).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13219 174719021 174751789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13220)) 174751789 174784557 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 174751789 174784557).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13220 174751789 174784557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13221)) 174784557 174817325 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 174784557 174817325).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13221 174784557 174817325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13223)) 174817325 174850093 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 174817325 174850093).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13223 174817325 174850093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 174719021 174784557).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 174719021 ≤ 174751789)
    (by decide : 174751789 ≤ 174784557) block0 block1

theorem join_0_1 : (twinPrimeSegment 174784557 174850093).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 174784557 ≤ 174817325)
    (by decide : 174817325 ≤ 174850093) block2 block3

theorem join_1_0 : (twinPrimeSegment 174719021 174850093).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 174719021 ≤ 174784557)
    (by decide : 174784557 ≤ 174850093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 174719021 174850093).card = 454 := join_1_0

end S083C05
end Sude.GeneratedTwinScan
