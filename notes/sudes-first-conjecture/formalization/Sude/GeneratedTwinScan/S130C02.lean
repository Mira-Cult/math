import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16520)) 272891949 272924717 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 272891949 272924717).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16520 272891949 272924717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16521)) 272924717 272957485 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 272924717 272957485).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16521 272924717 272957485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16522)) 272957485 272990253 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 272957485 272990253).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16522 272957485 272990253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16523)) 272990253 273023021 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 272990253 273023021).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16523 272990253 273023021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 272891949 272957485).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 272891949 ≤ 272924717)
    (by decide : 272924717 ≤ 272957485) block0 block1

theorem join_0_1 : (twinPrimeSegment 272957485 273023021).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 272957485 ≤ 272990253)
    (by decide : 272990253 ≤ 273023021) block2 block3

theorem join_1_0 : (twinPrimeSegment 272891949 273023021).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 272891949 ≤ 272957485)
    (by decide : 272957485 ≤ 273023021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 272891949 273023021).card = 465 := join_1_0

end S130C02
end Sude.GeneratedTwinScan
