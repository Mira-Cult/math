import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22324)) 498335789 498368557 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 498335789 498368557).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22324 498335789 498368557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22324)) 498368557 498401325 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 498368557 498401325).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22324 498368557 498401325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22325)) 498401325 498434093 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 498401325 498434093).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22325 498401325 498434093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22326)) 498434093 498466861 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 498434093 498466861).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22326 498434093 498466861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 498335789 498401325).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 498335789 ≤ 498368557)
    (by decide : 498368557 ≤ 498401325) block0 block1

theorem join_0_1 : (twinPrimeSegment 498401325 498466861).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 498401325 ≤ 498434093)
    (by decide : 498434093 ≤ 498466861) block2 block3

theorem join_1_0 : (twinPrimeSegment 498335789 498466861).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 498335789 ≤ 498401325)
    (by decide : 498401325 ≤ 498466861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 498335789 498466861).card = 448 := join_1_0

end S237C10
end Sude.GeneratedTwinScan
