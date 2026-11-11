import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19764)) 390594605 390627373 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 390594605 390627373).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19764 390594605 390627373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19765)) 390627373 390660141 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 390627373 390660141).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19765 390627373 390660141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19765)) 390660141 390692909 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 390660141 390692909).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19765 390660141 390692909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19766)) 390692909 390725677 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 390692909 390725677).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19766 390692909 390725677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 390594605 390660141).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 390594605 ≤ 390627373)
    (by decide : 390627373 ≤ 390660141) block0 block1

theorem join_0_1 : (twinPrimeSegment 390660141 390725677).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 390660141 ≤ 390692909)
    (by decide : 390692909 ≤ 390725677) block2 block3

theorem join_1_0 : (twinPrimeSegment 390594605 390725677).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 390594605 ≤ 390660141)
    (by decide : 390660141 ≤ 390725677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 390594605 390725677).card = 468 := join_1_0

end S186C04
end Sude.GeneratedTwinScan
