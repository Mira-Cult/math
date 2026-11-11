import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19899)) 395968557 396001325 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 395968557 396001325).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19899 395968557 396001325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19900)) 396001325 396034093 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 396001325 396034093).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19900 396001325 396034093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19901)) 396034093 396066861 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 396034093 396066861).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19901 396034093 396066861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19902)) 396066861 396099629 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 396066861 396099629).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19902 396066861 396099629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 395968557 396034093).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 395968557 ≤ 396001325)
    (by decide : 396001325 ≤ 396034093) block0 block1

theorem join_0_1 : (twinPrimeSegment 396034093 396099629).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 396034093 ≤ 396066861)
    (by decide : 396066861 ≤ 396099629) block2 block3

theorem join_1_0 : (twinPrimeSegment 395968557 396099629).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 395968557 ≤ 396034093)
    (by decide : 396034093 ≤ 396099629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 395968557 396099629).card = 412 := join_1_0

end S188C13
end Sude.GeneratedTwinScan
