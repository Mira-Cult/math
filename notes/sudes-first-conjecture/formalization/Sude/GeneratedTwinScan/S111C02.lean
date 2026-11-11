import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15266)) 233046061 233078829 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 233046061 233078829).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15266 233046061 233078829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15267)) 233078829 233111597 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 233078829 233111597).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15267 233078829 233111597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15269)) 233111597 233144365 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 233111597 233144365).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15269 233111597 233144365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15270)) 233144365 233177133 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 233144365 233177133).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15270 233144365 233177133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 233046061 233111597).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 233046061 ≤ 233078829)
    (by decide : 233078829 ≤ 233111597) block0 block1

theorem join_0_1 : (twinPrimeSegment 233111597 233177133).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 233111597 ≤ 233144365)
    (by decide : 233144365 ≤ 233177133) block2 block3

theorem join_1_0 : (twinPrimeSegment 233046061 233177133).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 233046061 ≤ 233111597)
    (by decide : 233111597 ≤ 233177133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 233046061 233177133).card = 473 := join_1_0

end S111C02
end Sude.GeneratedTwinScan
