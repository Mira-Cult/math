import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15501)) 240255021 240287789 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 240255021 240287789).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15501 240255021 240287789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15502)) 240287789 240320557 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 240287789 240320557).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15502 240287789 240320557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15503)) 240320557 240353325 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 240320557 240353325).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15503 240320557 240353325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15504)) 240353325 240386093 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 240353325 240386093).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15504 240353325 240386093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 240255021 240320557).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 240255021 ≤ 240287789)
    (by decide : 240287789 ≤ 240320557) block0 block1

theorem join_0_1 : (twinPrimeSegment 240320557 240386093).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 240320557 ≤ 240353325)
    (by decide : 240353325 ≤ 240386093) block2 block3

theorem join_1_0 : (twinPrimeSegment 240255021 240386093).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 240255021 ≤ 240320557)
    (by decide : 240320557 ≤ 240386093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 240255021 240386093).card = 489 := join_1_0

end S114C09
end Sude.GeneratedTwinScan
