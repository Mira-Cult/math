import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17946)) 322043949 322076717 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 322043949 322076717).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17946 322043949 322076717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17947)) 322076717 322109485 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 322076717 322109485).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17947 322076717 322109485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17948)) 322109485 322142253 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 322109485 322142253).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17948 322109485 322142253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17949)) 322142253 322175021 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 322142253 322175021).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17949 322142253 322175021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 322043949 322109485).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 322043949 ≤ 322076717)
    (by decide : 322076717 ≤ 322109485) block0 block1

theorem join_0_1 : (twinPrimeSegment 322109485 322175021).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 322109485 ≤ 322142253)
    (by decide : 322142253 ≤ 322175021) block2 block3

theorem join_1_0 : (twinPrimeSegment 322043949 322175021).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 322043949 ≤ 322109485)
    (by decide : 322109485 ≤ 322175021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 322043949 322175021).card = 465 := join_1_0

end S153C09
end Sude.GeneratedTwinScan
