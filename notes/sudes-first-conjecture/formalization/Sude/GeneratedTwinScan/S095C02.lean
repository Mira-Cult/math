import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S095C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14125)) 199491629 199524397 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 199491629 199524397).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14125 199491629 199524397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14126)) 199524397 199557165 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 199524397 199557165).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14126 199524397 199557165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14127)) 199557165 199589933 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 199557165 199589933).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14127 199557165 199589933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14128)) 199589933 199622701 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 199589933 199622701).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14128 199589933 199622701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 199491629 199557165).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 199491629 ≤ 199524397)
    (by decide : 199524397 ≤ 199557165) block0 block1

theorem join_0_1 : (twinPrimeSegment 199557165 199622701).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 199557165 ≤ 199589933)
    (by decide : 199589933 ≤ 199622701) block2 block3

theorem join_1_0 : (twinPrimeSegment 199491629 199622701).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 199491629 ≤ 199557165)
    (by decide : 199557165 ≤ 199622701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 199491629 199622701).card = 497 := join_1_0

end S095C02
end Sude.GeneratedTwinScan
