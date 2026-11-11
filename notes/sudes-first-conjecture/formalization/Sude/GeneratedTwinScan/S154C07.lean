import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17997)) 323878957 323911725 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 323878957 323911725).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17997 323878957 323911725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17998)) 323911725 323944493 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 323911725 323944493).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17998 323911725 323944493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17999)) 323944493 323977261 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 323944493 323977261).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17999 323944493 323977261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18000)) 323977261 324010029 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 323977261 324010029).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18000 323977261 324010029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 323878957 323944493).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 323878957 ≤ 323911725)
    (by decide : 323911725 ≤ 323944493) block0 block1

theorem join_0_1 : (twinPrimeSegment 323944493 324010029).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 323944493 ≤ 323977261)
    (by decide : 323977261 ≤ 324010029) block2 block3

theorem join_1_0 : (twinPrimeSegment 323878957 324010029).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 323878957 ≤ 323944493)
    (by decide : 323944493 ≤ 324010029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 323878957 324010029).card = 468 := join_1_0

end S154C07
end Sude.GeneratedTwinScan
