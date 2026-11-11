import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20867)) 435421229 435453997 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 435421229 435453997).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20867 435421229 435453997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20868)) 435453997 435486765 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 435453997 435486765).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20868 435453997 435486765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20869)) 435486765 435519533 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 435486765 435519533).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20869 435486765 435519533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20869)) 435519533 435552301 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 435519533 435552301).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20869 435519533 435552301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 435421229 435486765).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 435421229 ≤ 435453997)
    (by decide : 435453997 ≤ 435486765) block0 block1

theorem join_0_1 : (twinPrimeSegment 435486765 435552301).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 435486765 ≤ 435519533)
    (by decide : 435519533 ≤ 435552301) block2 block3

theorem join_1_0 : (twinPrimeSegment 435421229 435552301).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 435421229 ≤ 435486765)
    (by decide : 435486765 ≤ 435552301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 435421229 435552301).card = 449 := join_1_0

end S207C10
end Sude.GeneratedTwinScan
