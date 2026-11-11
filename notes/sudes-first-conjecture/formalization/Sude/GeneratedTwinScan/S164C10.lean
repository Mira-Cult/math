import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18581)) 345243693 345276461 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 345243693 345276461).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18581 345243693 345276461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18582)) 345276461 345309229 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 345276461 345309229).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18582 345276461 345309229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18583)) 345309229 345341997 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 345309229 345341997).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18583 345309229 345341997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18584)) 345341997 345374765 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 345341997 345374765).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18584 345341997 345374765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 345243693 345309229).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 345243693 ≤ 345276461)
    (by decide : 345276461 ≤ 345309229) block0 block1

theorem join_0_1 : (twinPrimeSegment 345309229 345374765).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 345309229 ≤ 345341997)
    (by decide : 345341997 ≤ 345374765) block2 block3

theorem join_1_0 : (twinPrimeSegment 345243693 345374765).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 345243693 ≤ 345309229)
    (by decide : 345309229 ≤ 345374765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 345243693 345374765).card = 435 := join_1_0

end S164C10
end Sude.GeneratedTwinScan
