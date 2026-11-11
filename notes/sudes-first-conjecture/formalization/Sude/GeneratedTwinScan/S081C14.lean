import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13104)) 171704365 171737133 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 171704365 171737133).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13104 171704365 171737133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13106)) 171737133 171769901 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 171737133 171769901).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13106 171737133 171769901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13107)) 171769901 171802669 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 171769901 171802669).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13107 171769901 171802669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13108)) 171802669 171835437 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 171802669 171835437).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13108 171802669 171835437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 171704365 171769901).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 171704365 ≤ 171737133)
    (by decide : 171737133 ≤ 171769901) block0 block1

theorem join_0_1 : (twinPrimeSegment 171769901 171835437).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 171769901 ≤ 171802669)
    (by decide : 171802669 ≤ 171835437) block2 block3

theorem join_1_0 : (twinPrimeSegment 171704365 171835437).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 171704365 ≤ 171769901)
    (by decide : 171769901 ≤ 171835437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 171704365 171835437).card = 504 := join_1_0

end S081C14
end Sude.GeneratedTwinScan
