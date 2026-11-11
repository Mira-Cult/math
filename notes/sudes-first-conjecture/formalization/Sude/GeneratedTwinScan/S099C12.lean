import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S099C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14464)) 209190957 209223725 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 209190957 209223725).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14464 209190957 209223725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14465)) 209223725 209256493 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 209223725 209256493).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14465 209223725 209256493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14466)) 209256493 209289261 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 209256493 209289261).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14466 209256493 209289261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14467)) 209289261 209322029 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 209289261 209322029).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14467 209289261 209322029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 209190957 209256493).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 209190957 ≤ 209223725)
    (by decide : 209223725 ≤ 209256493) block0 block1

theorem join_0_1 : (twinPrimeSegment 209256493 209322029).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 209256493 ≤ 209289261)
    (by decide : 209289261 ≤ 209322029) block2 block3

theorem join_1_0 : (twinPrimeSegment 209190957 209322029).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 209190957 ≤ 209256493)
    (by decide : 209256493 ≤ 209322029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 209190957 209322029).card = 487 := join_1_0

end S099C12
end Sude.GeneratedTwinScan
