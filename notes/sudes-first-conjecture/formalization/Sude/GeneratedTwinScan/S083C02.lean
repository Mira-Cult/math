import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13204)) 174325805 174358573 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 174325805 174358573).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13204 174325805 174358573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13205)) 174358573 174391341 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 174358573 174391341).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13205 174358573 174391341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13206)) 174391341 174424109 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 174391341 174424109).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13206 174391341 174424109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13208)) 174424109 174456877 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 174424109 174456877).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13208 174424109 174456877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 174325805 174391341).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 174325805 ≤ 174358573)
    (by decide : 174358573 ≤ 174391341) block0 block1

theorem join_0_1 : (twinPrimeSegment 174391341 174456877).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 174391341 ≤ 174424109)
    (by decide : 174424109 ≤ 174456877) block2 block3

theorem join_1_0 : (twinPrimeSegment 174325805 174456877).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 174325805 ≤ 174391341)
    (by decide : 174391341 ≤ 174456877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 174325805 174456877).card = 454 := join_1_0

end S083C02
end Sude.GeneratedTwinScan
