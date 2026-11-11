import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16670)) 277872685 277905453 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 277872685 277905453).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16670 277872685 277905453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16671)) 277905453 277938221 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 277905453 277938221).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16671 277905453 277938221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16672)) 277938221 277970989 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 277938221 277970989).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16672 277938221 277970989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16673)) 277970989 278003757 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 277970989 278003757).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16673 277970989 278003757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 277872685 277938221).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 277872685 ≤ 277905453)
    (by decide : 277905453 ≤ 277938221) block0 block1

theorem join_0_1 : (twinPrimeSegment 277938221 278003757).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 277938221 ≤ 277970989)
    (by decide : 277970989 ≤ 278003757) block2 block3

theorem join_1_0 : (twinPrimeSegment 277872685 278003757).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 277872685 ≤ 277938221)
    (by decide : 277938221 ≤ 278003757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 277872685 278003757).card = 468 := join_1_0

end S132C08
end Sude.GeneratedTwinScan
