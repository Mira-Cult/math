import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15669)) 245497901 245530669 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 245497901 245530669).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15669 245497901 245530669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15670)) 245530669 245563437 = 84 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 245530669 245563437).card = 84 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15670 245530669 245563437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15671)) 245563437 245596205 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 245563437 245596205).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15671 245563437 245596205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15672)) 245596205 245628973 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 245596205 245628973).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15672 245596205 245628973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 245497901 245563437).card = 190 := by
  simpa using combineTwinPrimeSegments (by decide : 245497901 ≤ 245530669)
    (by decide : 245530669 ≤ 245563437) block0 block1

theorem join_0_1 : (twinPrimeSegment 245563437 245628973).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 245563437 ≤ 245596205)
    (by decide : 245596205 ≤ 245628973) block2 block3

theorem join_1_0 : (twinPrimeSegment 245497901 245628973).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 245497901 ≤ 245563437)
    (by decide : 245563437 ≤ 245628973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 245497901 245628973).card = 414 := join_1_0

end S117C01
end Sude.GeneratedTwinScan
