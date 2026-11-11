import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14523)) 210894893 210927661 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 210894893 210927661).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14523 210894893 210927661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14524)) 210927661 210960429 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 210927661 210960429).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14524 210927661 210960429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14525)) 210960429 210993197 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 210960429 210993197).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14525 210960429 210993197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14526)) 210993197 211025965 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 210993197 211025965).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14526 210993197 211025965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 210894893 210960429).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 210894893 ≤ 210927661)
    (by decide : 210927661 ≤ 210960429) block0 block1

theorem join_0_1 : (twinPrimeSegment 210960429 211025965).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 210960429 ≤ 210993197)
    (by decide : 210993197 ≤ 211025965) block2 block3

theorem join_1_0 : (twinPrimeSegment 210894893 211025965).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 210894893 ≤ 210960429)
    (by decide : 210960429 ≤ 211025965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 210894893 211025965).card = 467 := join_1_0

end S100C09
end Sude.GeneratedTwinScan
