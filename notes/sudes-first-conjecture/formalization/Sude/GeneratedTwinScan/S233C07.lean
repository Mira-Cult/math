import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22126)) 489553965 489586733 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 489553965 489586733).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22126 489553965 489586733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22127)) 489586733 489619501 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 489586733 489619501).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22127 489586733 489619501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22128)) 489619501 489652269 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 489619501 489652269).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22128 489619501 489652269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22128)) 489652269 489685037 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 489652269 489685037).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22128 489652269 489685037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 489553965 489619501).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 489553965 ≤ 489586733)
    (by decide : 489586733 ≤ 489619501) block0 block1

theorem join_0_1 : (twinPrimeSegment 489619501 489685037).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 489619501 ≤ 489652269)
    (by decide : 489652269 ≤ 489685037) block2 block3

theorem join_1_0 : (twinPrimeSegment 489553965 489685037).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 489553965 ≤ 489619501)
    (by decide : 489619501 ≤ 489685037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 489553965 489685037).card = 463 := join_1_0

end S233C07
end Sude.GeneratedTwinScan
