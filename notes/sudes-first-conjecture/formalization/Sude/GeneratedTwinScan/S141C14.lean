import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17250)) 297533485 297566253 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 297533485 297566253).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17250 297533485 297566253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17251)) 297566253 297599021 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 297566253 297599021).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17251 297566253 297599021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17252)) 297599021 297631789 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 297599021 297631789).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17252 297599021 297631789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17252)) 297631789 297664557 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 297631789 297664557).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17252 297631789 297664557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 297533485 297599021).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 297533485 ≤ 297566253)
    (by decide : 297566253 ≤ 297599021) block0 block1

theorem join_0_1 : (twinPrimeSegment 297599021 297664557).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 297599021 ≤ 297631789)
    (by decide : 297631789 ≤ 297664557) block2 block3

theorem join_1_0 : (twinPrimeSegment 297533485 297664557).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 297533485 ≤ 297599021)
    (by decide : 297599021 ≤ 297664557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 297533485 297664557).card = 463 := join_1_0

end S141C14
end Sude.GeneratedTwinScan
