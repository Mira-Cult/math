import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13119)) 172097581 172130349 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 172097581 172130349).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13119 172097581 172130349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13121)) 172130349 172163117 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 172130349 172163117).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13121 172130349 172163117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13122)) 172163117 172195885 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 172163117 172195885).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13122 172163117 172195885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13123)) 172195885 172228653 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 172195885 172228653).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13123 172195885 172228653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 172097581 172163117).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 172097581 ≤ 172130349)
    (by decide : 172130349 ≤ 172163117) block0 block1

theorem join_0_1 : (twinPrimeSegment 172163117 172228653).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 172163117 ≤ 172195885)
    (by decide : 172195885 ≤ 172228653) block2 block3

theorem join_1_0 : (twinPrimeSegment 172097581 172228653).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 172097581 ≤ 172163117)
    (by decide : 172163117 ≤ 172228653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 172097581 172228653).card = 468 := join_1_0

end S082C01
end Sude.GeneratedTwinScan
