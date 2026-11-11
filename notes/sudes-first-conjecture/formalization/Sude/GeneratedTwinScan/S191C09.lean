import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20044)) 401735725 401768493 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 401735725 401768493).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20044 401735725 401768493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20044)) 401768493 401801261 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 401768493 401801261).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20044 401768493 401801261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20045)) 401801261 401834029 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 401801261 401834029).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20045 401801261 401834029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20046)) 401834029 401866797 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 401834029 401866797).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20046 401834029 401866797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 401735725 401801261).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 401735725 ≤ 401768493)
    (by decide : 401768493 ≤ 401801261) block0 block1

theorem join_0_1 : (twinPrimeSegment 401801261 401866797).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 401801261 ≤ 401834029)
    (by decide : 401834029 ≤ 401866797) block2 block3

theorem join_1_0 : (twinPrimeSegment 401735725 401866797).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 401735725 ≤ 401801261)
    (by decide : 401801261 ≤ 401866797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 401735725 401866797).card = 442 := join_1_0

end S191C09
end Sude.GeneratedTwinScan
