import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S196C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20281)) 411303981 411336749 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 411303981 411336749).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20281 411303981 411336749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20282)) 411336749 411369517 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 411336749 411369517).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20282 411336749 411369517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20283)) 411369517 411402285 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 411369517 411402285).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20283 411369517 411402285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20283)) 411402285 411435053 = 79 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 411402285 411435053).card = 79 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20283 411402285 411435053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 411303981 411369517).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 411303981 ≤ 411336749)
    (by decide : 411336749 ≤ 411369517) block0 block1

theorem join_0_1 : (twinPrimeSegment 411369517 411435053).card = 191 := by
  simpa using combineTwinPrimeSegments (by decide : 411369517 ≤ 411402285)
    (by decide : 411402285 ≤ 411435053) block2 block3

theorem join_1_0 : (twinPrimeSegment 411303981 411435053).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 411303981 ≤ 411369517)
    (by decide : 411369517 ≤ 411435053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 411303981 411435053).card = 429 := join_1_0

end S196C02
end Sude.GeneratedTwinScan
