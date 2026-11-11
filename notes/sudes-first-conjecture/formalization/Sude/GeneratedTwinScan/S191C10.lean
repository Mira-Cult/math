import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20047)) 401866797 401899565 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 401866797 401899565).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20047 401866797 401899565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20048)) 401899565 401932333 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 401899565 401932333).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20048 401899565 401932333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20049)) 401932333 401965101 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 401932333 401965101).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20049 401932333 401965101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20049)) 401965101 401997869 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 401965101 401997869).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20049 401965101 401997869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 401866797 401932333).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 401866797 ≤ 401899565)
    (by decide : 401899565 ≤ 401932333) block0 block1

theorem join_0_1 : (twinPrimeSegment 401932333 401997869).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 401932333 ≤ 401965101)
    (by decide : 401965101 ≤ 401997869) block2 block3

theorem join_1_0 : (twinPrimeSegment 401866797 401997869).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 401866797 ≤ 401932333)
    (by decide : 401932333 ≤ 401997869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 401866797 401997869).card = 423 := join_1_0

end S191C10
end Sude.GeneratedTwinScan
