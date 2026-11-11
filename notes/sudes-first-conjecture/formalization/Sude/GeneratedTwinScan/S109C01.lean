import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15124)) 228720685 228753453 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 228720685 228753453).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15124 228720685 228753453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15125)) 228753453 228786221 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 228753453 228786221).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15125 228753453 228786221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15126)) 228786221 228818989 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 228786221 228818989).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15126 228786221 228818989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15127)) 228818989 228851757 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 228818989 228851757).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15127 228818989 228851757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 228720685 228786221).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 228720685 ≤ 228753453)
    (by decide : 228753453 ≤ 228786221) block0 block1

theorem join_0_1 : (twinPrimeSegment 228786221 228851757).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 228786221 ≤ 228818989)
    (by decide : 228818989 ≤ 228851757) block2 block3

theorem join_1_0 : (twinPrimeSegment 228720685 228851757).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 228720685 ≤ 228786221)
    (by decide : 228786221 ≤ 228851757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 228720685 228851757).card = 456 := join_1_0

end S109C01
end Sude.GeneratedTwinScan
