import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17487)) 305791021 305823789 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 305791021 305823789).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17487 305791021 305823789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17488)) 305823789 305856557 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 305823789 305856557).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17488 305823789 305856557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17489)) 305856557 305889325 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 305856557 305889325).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17489 305856557 305889325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17490)) 305889325 305922093 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 305889325 305922093).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17490 305889325 305922093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 305791021 305856557).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 305791021 ≤ 305823789)
    (by decide : 305823789 ≤ 305856557) block0 block1

theorem join_0_1 : (twinPrimeSegment 305856557 305922093).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 305856557 ≤ 305889325)
    (by decide : 305889325 ≤ 305922093) block2 block3

theorem join_1_0 : (twinPrimeSegment 305791021 305922093).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 305791021 ≤ 305856557)
    (by decide : 305856557 ≤ 305922093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 305791021 305922093).card = 446 := join_1_0

end S145C13
end Sude.GeneratedTwinScan
