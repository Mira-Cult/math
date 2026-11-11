import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22141)) 490209325 490242093 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 490209325 490242093).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22141 490209325 490242093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22142)) 490242093 490274861 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 490242093 490274861).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22142 490242093 490274861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22142)) 490274861 490307629 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 490274861 490307629).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22142 490274861 490307629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22143)) 490307629 490340397 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 490307629 490340397).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22143 490307629 490340397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 490209325 490274861).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 490209325 ≤ 490242093)
    (by decide : 490242093 ≤ 490274861) block0 block1

theorem join_0_1 : (twinPrimeSegment 490274861 490340397).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 490274861 ≤ 490307629)
    (by decide : 490307629 ≤ 490340397) block2 block3

theorem join_1_0 : (twinPrimeSegment 490209325 490340397).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 490209325 ≤ 490274861)
    (by decide : 490274861 ≤ 490340397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 490209325 490340397).card = 418 := join_1_0

end S233C12
end Sude.GeneratedTwinScan
