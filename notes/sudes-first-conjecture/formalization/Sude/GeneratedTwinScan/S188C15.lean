import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19906)) 396230701 396263469 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 396230701 396263469).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19906 396230701 396263469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19907)) 396263469 396296237 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 396263469 396296237).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19907 396263469 396296237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19908)) 396296237 396329005 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 396296237 396329005).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19908 396296237 396329005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19908)) 396329005 396361773 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 396329005 396361773).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19908 396329005 396361773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 396230701 396296237).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 396230701 ≤ 396263469)
    (by decide : 396263469 ≤ 396296237) block0 block1

theorem join_0_1 : (twinPrimeSegment 396296237 396361773).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 396296237 ≤ 396329005)
    (by decide : 396329005 ≤ 396361773) block2 block3

theorem join_1_0 : (twinPrimeSegment 396230701 396361773).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 396230701 ≤ 396296237)
    (by decide : 396296237 ≤ 396361773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 396230701 396361773).card = 454 := join_1_0

end S188C15
end Sude.GeneratedTwinScan
