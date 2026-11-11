import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S222C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21580)) 465698861 465731629 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 465698861 465731629).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21580 465698861 465731629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21581)) 465731629 465764397 = 90 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 465731629 465764397).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21581 465731629 465764397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21582)) 465764397 465797165 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 465764397 465797165).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21582 465764397 465797165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21583)) 465797165 465829933 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 465797165 465829933).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21583 465797165 465829933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 465698861 465764397).card = 194 := by
  simpa using combineTwinPrimeSegments (by decide : 465698861 ≤ 465731629)
    (by decide : 465731629 ≤ 465764397) block0 block1

theorem join_0_1 : (twinPrimeSegment 465764397 465829933).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 465764397 ≤ 465797165)
    (by decide : 465797165 ≤ 465829933) block2 block3

theorem join_1_0 : (twinPrimeSegment 465698861 465829933).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 465698861 ≤ 465764397)
    (by decide : 465764397 ≤ 465829933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 465698861 465829933).card = 422 := join_1_0

end S222C01
end Sude.GeneratedTwinScan
