import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21449)) 460062765 460095533 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 460062765 460095533).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21449 460062765 460095533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21450)) 460095533 460128301 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 460095533 460128301).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21450 460095533 460128301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21451)) 460128301 460161069 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 460128301 460161069).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21451 460128301 460161069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21452)) 460161069 460193837 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 460161069 460193837).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21452 460161069 460193837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 460062765 460128301).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 460062765 ≤ 460095533)
    (by decide : 460095533 ≤ 460128301) block0 block1

theorem join_0_1 : (twinPrimeSegment 460128301 460193837).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 460128301 ≤ 460161069)
    (by decide : 460161069 ≤ 460193837) block2 block3

theorem join_1_0 : (twinPrimeSegment 460062765 460193837).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 460062765 ≤ 460128301)
    (by decide : 460128301 ≤ 460193837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 460062765 460193837).card = 415 := join_1_0

end S219C06
end Sude.GeneratedTwinScan
