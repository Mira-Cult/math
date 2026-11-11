import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14901)) 222036013 222068781 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 222036013 222068781).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14901 222036013 222068781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14903)) 222068781 222101549 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 222068781 222101549).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14903 222068781 222101549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14904)) 222101549 222134317 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 222101549 222134317).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14904 222101549 222134317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14905)) 222134317 222167085 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 222134317 222167085).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14905 222134317 222167085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 222036013 222101549).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 222036013 ≤ 222068781)
    (by decide : 222068781 ≤ 222101549) block0 block1

theorem join_0_1 : (twinPrimeSegment 222101549 222167085).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 222101549 ≤ 222134317)
    (by decide : 222134317 ≤ 222167085) block2 block3

theorem join_1_0 : (twinPrimeSegment 222036013 222167085).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 222036013 ≤ 222101549)
    (by decide : 222101549 ≤ 222167085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 222036013 222167085).card = 477 := join_1_0

end S105C14
end Sude.GeneratedTwinScan
