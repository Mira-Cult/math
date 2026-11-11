import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14550)) 211681325 211714093 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 211681325 211714093).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14550 211681325 211714093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14551)) 211714093 211746861 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 211714093 211746861).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14551 211714093 211746861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14552)) 211746861 211779629 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 211746861 211779629).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14552 211746861 211779629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14553)) 211779629 211812397 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 211779629 211812397).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14553 211779629 211812397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 211681325 211746861).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 211681325 ≤ 211714093)
    (by decide : 211714093 ≤ 211746861) block0 block1

theorem join_0_1 : (twinPrimeSegment 211746861 211812397).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 211746861 ≤ 211779629)
    (by decide : 211779629 ≤ 211812397) block2 block3

theorem join_1_0 : (twinPrimeSegment 211681325 211812397).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 211681325 ≤ 211746861)
    (by decide : 211746861 ≤ 211812397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 211681325 211812397).card = 483 := join_1_0

end S100C15
end Sude.GeneratedTwinScan
