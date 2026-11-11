import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14963)) 223871021 223903789 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 223871021 223903789).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14963 223871021 223903789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14964)) 223903789 223936557 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 223903789 223936557).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14964 223903789 223936557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14965)) 223936557 223969325 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 223936557 223969325).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14965 223936557 223969325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14966)) 223969325 224002093 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 223969325 224002093).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14966 223969325 224002093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 223871021 223936557).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 223871021 ≤ 223903789)
    (by decide : 223903789 ≤ 223936557) block0 block1

theorem join_0_1 : (twinPrimeSegment 223936557 224002093).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 223936557 ≤ 223969325)
    (by decide : 223969325 ≤ 224002093) block2 block3

theorem join_1_0 : (twinPrimeSegment 223871021 224002093).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 223871021 ≤ 223936557)
    (by decide : 223936557 ≤ 224002093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 223871021 224002093).card = 482 := join_1_0

end S106C12
end Sude.GeneratedTwinScan
