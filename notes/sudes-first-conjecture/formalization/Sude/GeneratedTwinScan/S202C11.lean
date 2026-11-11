import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20617)) 425066541 425099309 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 425066541 425099309).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20617 425066541 425099309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20618)) 425099309 425132077 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 425099309 425132077).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20618 425099309 425132077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20619)) 425132077 425164845 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 425132077 425164845).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20619 425132077 425164845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20620)) 425164845 425197613 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 425164845 425197613).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20620 425164845 425197613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 425066541 425132077).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 425066541 ≤ 425099309)
    (by decide : 425099309 ≤ 425132077) block0 block1

theorem join_0_1 : (twinPrimeSegment 425132077 425197613).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 425132077 ≤ 425164845)
    (by decide : 425164845 ≤ 425197613) block2 block3

theorem join_1_0 : (twinPrimeSegment 425066541 425197613).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 425066541 ≤ 425132077)
    (by decide : 425132077 ≤ 425197613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 425066541 425197613).card = 437 := join_1_0

end S202C11
end Sude.GeneratedTwinScan
