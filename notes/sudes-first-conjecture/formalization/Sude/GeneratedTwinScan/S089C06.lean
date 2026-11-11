import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13691)) 187433005 187465773 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 187433005 187465773).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13691 187433005 187465773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13693)) 187465773 187498541 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 187465773 187498541).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13693 187465773 187498541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13694)) 187498541 187531309 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 187498541 187531309).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13694 187498541 187531309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13695)) 187531309 187564077 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 187531309 187564077).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13695 187531309 187564077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 187433005 187498541).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 187433005 ≤ 187465773)
    (by decide : 187465773 ≤ 187498541) block0 block1

theorem join_0_1 : (twinPrimeSegment 187498541 187564077).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 187498541 ≤ 187531309)
    (by decide : 187531309 ≤ 187564077) block2 block3

theorem join_1_0 : (twinPrimeSegment 187433005 187564077).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 187433005 ≤ 187498541)
    (by decide : 187498541 ≤ 187564077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 187433005 187564077).card = 479 := join_1_0

end S089C06
end Sude.GeneratedTwinScan
