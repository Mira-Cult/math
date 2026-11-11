import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17843)) 318373933 318406701 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 318373933 318406701).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17843 318373933 318406701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17844)) 318406701 318439469 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 318406701 318439469).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17844 318406701 318439469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17845)) 318439469 318472237 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 318439469 318472237).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17845 318439469 318472237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17846)) 318472237 318505005 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 318472237 318505005).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17846 318472237 318505005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 318373933 318439469).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 318373933 ≤ 318406701)
    (by decide : 318406701 ≤ 318439469) block0 block1

theorem join_0_1 : (twinPrimeSegment 318439469 318505005).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 318439469 ≤ 318472237)
    (by decide : 318472237 ≤ 318505005) block2 block3

theorem join_1_0 : (twinPrimeSegment 318373933 318505005).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 318373933 ≤ 318439469)
    (by decide : 318439469 ≤ 318505005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 318373933 318505005).card = 423 := join_1_0

end S151C13
end Sude.GeneratedTwinScan
