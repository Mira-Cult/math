import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15951)) 254410797 254443565 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 254410797 254443565).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15951 254410797 254443565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15952)) 254443565 254476333 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 254443565 254476333).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15952 254443565 254476333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15953)) 254476333 254509101 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 254476333 254509101).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15953 254476333 254509101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15954)) 254509101 254541869 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 254509101 254541869).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15954 254509101 254541869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 254410797 254476333).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 254410797 ≤ 254443565)
    (by decide : 254443565 ≤ 254476333) block0 block1

theorem join_0_1 : (twinPrimeSegment 254476333 254541869).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 254476333 ≤ 254509101)
    (by decide : 254509101 ≤ 254541869) block2 block3

theorem join_1_0 : (twinPrimeSegment 254410797 254541869).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 254410797 ≤ 254476333)
    (by decide : 254476333 ≤ 254541869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 254410797 254541869).card = 480 := join_1_0

end S121C05
end Sude.GeneratedTwinScan
