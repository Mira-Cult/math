import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21711)) 471334957 471367725 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 471334957 471367725).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21711 471334957 471367725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21711)) 471367725 471400493 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 471367725 471400493).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21711 471367725 471400493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21712)) 471400493 471433261 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 471400493 471433261).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21712 471400493 471433261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21713)) 471433261 471466029 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 471433261 471466029).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21713 471433261 471466029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 471334957 471400493).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 471334957 ≤ 471367725)
    (by decide : 471367725 ≤ 471400493) block0 block1

theorem join_0_1 : (twinPrimeSegment 471400493 471466029).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 471400493 ≤ 471433261)
    (by decide : 471433261 ≤ 471466029) block2 block3

theorem join_1_0 : (twinPrimeSegment 471334957 471466029).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 471334957 ≤ 471400493)
    (by decide : 471400493 ≤ 471466029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 471334957 471466029).card = 439 := join_1_0

end S224C12
end Sude.GeneratedTwinScan
