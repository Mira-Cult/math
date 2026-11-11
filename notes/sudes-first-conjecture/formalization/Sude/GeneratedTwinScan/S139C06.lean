import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17097)) 292290605 292323373 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 292290605 292323373).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17097 292290605 292323373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17098)) 292323373 292356141 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 292323373 292356141).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17098 292323373 292356141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17099)) 292356141 292388909 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 292356141 292388909).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17099 292356141 292388909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17100)) 292388909 292421677 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 292388909 292421677).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17100 292388909 292421677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 292290605 292356141).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 292290605 ≤ 292323373)
    (by decide : 292323373 ≤ 292356141) block0 block1

theorem join_0_1 : (twinPrimeSegment 292356141 292421677).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 292356141 ≤ 292388909)
    (by decide : 292388909 ≤ 292421677) block2 block3

theorem join_1_0 : (twinPrimeSegment 292290605 292421677).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 292290605 ≤ 292356141)
    (by decide : 292356141 ≤ 292421677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 292290605 292421677).card = 473 := join_1_0

end S139C06
end Sude.GeneratedTwinScan
