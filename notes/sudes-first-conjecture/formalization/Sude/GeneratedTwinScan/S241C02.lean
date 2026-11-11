import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22487)) 505675821 505708589 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 505675821 505708589).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22487 505675821 505708589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22488)) 505708589 505741357 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 505708589 505741357).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22488 505708589 505741357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22489)) 505741357 505774125 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 505741357 505774125).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22489 505741357 505774125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22490)) 505774125 505806893 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 505774125 505806893).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22490 505774125 505806893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 505675821 505741357).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 505675821 ≤ 505708589)
    (by decide : 505708589 ≤ 505741357) block0 block1

theorem join_0_1 : (twinPrimeSegment 505741357 505806893).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 505741357 ≤ 505774125)
    (by decide : 505774125 ≤ 505806893) block2 block3

theorem join_1_0 : (twinPrimeSegment 505675821 505806893).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 505675821 ≤ 505741357)
    (by decide : 505741357 ≤ 505806893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 505675821 505806893).card = 453 := join_1_0

end S241C02
end Sude.GeneratedTwinScan
