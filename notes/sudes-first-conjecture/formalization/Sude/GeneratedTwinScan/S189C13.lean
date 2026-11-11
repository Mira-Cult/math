import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19952)) 398065709 398098477 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 398065709 398098477).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19952 398065709 398098477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19953)) 398098477 398131245 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 398098477 398131245).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19953 398098477 398131245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19954)) 398131245 398164013 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 398131245 398164013).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19954 398131245 398164013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19954)) 398164013 398196781 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 398164013 398196781).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19954 398164013 398196781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 398065709 398131245).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 398065709 ≤ 398098477)
    (by decide : 398098477 ≤ 398131245) block0 block1

theorem join_0_1 : (twinPrimeSegment 398131245 398196781).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 398131245 ≤ 398164013)
    (by decide : 398164013 ≤ 398196781) block2 block3

theorem join_1_0 : (twinPrimeSegment 398065709 398196781).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 398065709 ≤ 398131245)
    (by decide : 398131245 ≤ 398196781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 398065709 398196781).card = 444 := join_1_0

end S189C13
end Sude.GeneratedTwinScan
