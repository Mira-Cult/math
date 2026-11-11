import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14500)) 210239533 210272301 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 210239533 210272301).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14500 210239533 210272301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14501)) 210272301 210305069 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 210272301 210305069).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14501 210272301 210305069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14503)) 210305069 210337837 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 210305069 210337837).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14503 210305069 210337837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14504)) 210337837 210370605 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 210337837 210370605).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14504 210337837 210370605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 210239533 210305069).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 210239533 ≤ 210272301)
    (by decide : 210272301 ≤ 210305069) block0 block1

theorem join_0_1 : (twinPrimeSegment 210305069 210370605).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 210305069 ≤ 210337837)
    (by decide : 210337837 ≤ 210370605) block2 block3

theorem join_1_0 : (twinPrimeSegment 210239533 210370605).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 210239533 ≤ 210305069)
    (by decide : 210305069 ≤ 210370605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 210239533 210370605).card = 488 := join_1_0

end S100C04
end Sude.GeneratedTwinScan
