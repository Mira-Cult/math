import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17386)) 302252077 302284845 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 302252077 302284845).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17386 302252077 302284845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17387)) 302284845 302317613 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 302284845 302317613).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17387 302284845 302317613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17388)) 302317613 302350381 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 302317613 302350381).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17388 302317613 302350381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17389)) 302350381 302383149 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 302350381 302383149).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17389 302350381 302383149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 302252077 302317613).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 302252077 ≤ 302284845)
    (by decide : 302284845 ≤ 302317613) block0 block1

theorem join_0_1 : (twinPrimeSegment 302317613 302383149).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 302317613 ≤ 302350381)
    (by decide : 302350381 ≤ 302383149) block2 block3

theorem join_1_0 : (twinPrimeSegment 302252077 302383149).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 302252077 ≤ 302317613)
    (by decide : 302317613 ≤ 302383149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 302252077 302383149).card = 452 := join_1_0

end S144C02
end Sude.GeneratedTwinScan
