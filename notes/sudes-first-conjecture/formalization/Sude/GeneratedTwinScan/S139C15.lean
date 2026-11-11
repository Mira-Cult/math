import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17131)) 293470253 293503021 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 293470253 293503021).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17131 293470253 293503021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17132)) 293503021 293535789 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 293503021 293535789).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17132 293503021 293535789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17133)) 293535789 293568557 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 293535789 293568557).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17133 293535789 293568557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17134)) 293568557 293601325 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 293568557 293601325).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17134 293568557 293601325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 293470253 293535789).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 293470253 ≤ 293503021)
    (by decide : 293503021 ≤ 293535789) block0 block1

theorem join_0_1 : (twinPrimeSegment 293535789 293601325).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 293535789 ≤ 293568557)
    (by decide : 293568557 ≤ 293601325) block2 block3

theorem join_1_0 : (twinPrimeSegment 293470253 293601325).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 293470253 ≤ 293535789)
    (by decide : 293535789 ≤ 293601325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 293470253 293601325).card = 481 := join_1_0

end S139C15
end Sude.GeneratedTwinScan
