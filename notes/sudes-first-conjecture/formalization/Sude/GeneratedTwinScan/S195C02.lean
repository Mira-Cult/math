import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20229)) 409206829 409239597 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 409206829 409239597).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20229 409206829 409239597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20230)) 409239597 409272365 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 409239597 409272365).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20230 409239597 409272365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20231)) 409272365 409305133 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 409272365 409305133).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20231 409272365 409305133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20232)) 409305133 409337901 = 90 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 409305133 409337901).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20232 409305133 409337901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 409206829 409272365).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 409206829 ≤ 409239597)
    (by decide : 409239597 ≤ 409272365) block0 block1

theorem join_0_1 : (twinPrimeSegment 409272365 409337901).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 409272365 ≤ 409305133)
    (by decide : 409305133 ≤ 409337901) block2 block3

theorem join_1_0 : (twinPrimeSegment 409206829 409337901).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 409206829 ≤ 409272365)
    (by decide : 409272365 ≤ 409337901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 409206829 409337901).card = 416 := join_1_0

end S195C02
end Sude.GeneratedTwinScan
