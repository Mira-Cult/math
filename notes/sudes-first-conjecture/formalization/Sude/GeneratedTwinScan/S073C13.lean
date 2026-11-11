import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12443)) 154796077 154828845 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 154796077 154828845).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12443 154796077 154828845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12444)) 154828845 154861613 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 154828845 154861613).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12444 154828845 154861613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12445)) 154861613 154894381 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 154861613 154894381).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12445 154861613 154894381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12446)) 154894381 154927149 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 154894381 154927149).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12446 154894381 154927149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 154796077 154861613).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 154796077 ≤ 154828845)
    (by decide : 154828845 ≤ 154861613) block0 block1

theorem join_0_1 : (twinPrimeSegment 154861613 154927149).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 154861613 ≤ 154894381)
    (by decide : 154894381 ≤ 154927149) block2 block3

theorem join_1_0 : (twinPrimeSegment 154796077 154927149).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 154796077 ≤ 154861613)
    (by decide : 154861613 ≤ 154927149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 154796077 154927149).card = 486 := join_1_0

end S073C13
end Sude.GeneratedTwinScan
