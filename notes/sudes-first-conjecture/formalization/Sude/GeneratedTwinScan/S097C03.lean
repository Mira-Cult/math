import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14277)) 203817005 203849773 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 203817005 203849773).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14277 203817005 203849773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14278)) 203849773 203882541 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 203849773 203882541).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14278 203849773 203882541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14279)) 203882541 203915309 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 203882541 203915309).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14279 203882541 203915309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14281)) 203915309 203948077 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 203915309 203948077).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14281 203915309 203948077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 203817005 203882541).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 203817005 ≤ 203849773)
    (by decide : 203849773 ≤ 203882541) block0 block1

theorem join_0_1 : (twinPrimeSegment 203882541 203948077).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 203882541 ≤ 203915309)
    (by decide : 203915309 ≤ 203948077) block2 block3

theorem join_1_0 : (twinPrimeSegment 203817005 203948077).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 203817005 ≤ 203882541)
    (by decide : 203882541 ≤ 203948077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 203817005 203948077).card = 453 := join_1_0

end S097C03
end Sude.GeneratedTwinScan
