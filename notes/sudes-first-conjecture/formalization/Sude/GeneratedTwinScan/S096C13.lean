import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14250)) 203030573 203063341 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 203030573 203063341).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14250 203030573 203063341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14251)) 203063341 203096109 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 203063341 203096109).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14251 203063341 203096109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14252)) 203096109 203128877 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 203096109 203128877).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14252 203096109 203128877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14253)) 203128877 203161645 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 203128877 203161645).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14253 203128877 203161645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 203030573 203096109).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 203030573 ≤ 203063341)
    (by decide : 203063341 ≤ 203096109) block0 block1

theorem join_0_1 : (twinPrimeSegment 203096109 203161645).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 203096109 ≤ 203128877)
    (by decide : 203128877 ≤ 203161645) block2 block3

theorem join_1_0 : (twinPrimeSegment 203030573 203161645).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 203030573 ≤ 203096109)
    (by decide : 203096109 ≤ 203161645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 203030573 203161645).card = 478 := join_1_0

end S096C13
end Sude.GeneratedTwinScan
