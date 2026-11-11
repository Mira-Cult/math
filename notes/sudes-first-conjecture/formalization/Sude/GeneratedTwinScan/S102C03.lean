import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14640)) 214302765 214335533 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 214302765 214335533).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14640 214302765 214335533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14641)) 214335533 214368301 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 214335533 214368301).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14641 214335533 214368301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14642)) 214368301 214401069 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 214368301 214401069).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14642 214368301 214401069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14643)) 214401069 214433837 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 214401069 214433837).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14643 214401069 214433837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 214302765 214368301).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 214302765 ≤ 214335533)
    (by decide : 214335533 ≤ 214368301) block0 block1

theorem join_0_1 : (twinPrimeSegment 214368301 214433837).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 214368301 ≤ 214401069)
    (by decide : 214401069 ≤ 214433837) block2 block3

theorem join_1_0 : (twinPrimeSegment 214302765 214433837).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 214302765 ≤ 214368301)
    (by decide : 214368301 ≤ 214433837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 214302765 214433837).card = 475 := join_1_0

end S102C03
end Sude.GeneratedTwinScan
