import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16536)) 273416237 273449005 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 273416237 273449005).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16536 273416237 273449005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16537)) 273449005 273481773 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 273449005 273481773).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16537 273449005 273481773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16538)) 273481773 273514541 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 273481773 273514541).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16538 273481773 273514541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16539)) 273514541 273547309 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 273514541 273547309).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16539 273514541 273547309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 273416237 273481773).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 273416237 ≤ 273449005)
    (by decide : 273449005 ≤ 273481773) block0 block1

theorem join_0_1 : (twinPrimeSegment 273481773 273547309).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 273481773 ≤ 273514541)
    (by decide : 273514541 ≤ 273547309) block2 block3

theorem join_1_0 : (twinPrimeSegment 273416237 273547309).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 273416237 ≤ 273481773)
    (by decide : 273481773 ≤ 273547309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 273416237 273547309).card = 448 := join_1_0

end S130C06
end Sude.GeneratedTwinScan
