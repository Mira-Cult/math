import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13293)) 176685101 176717869 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 176685101 176717869).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13293 176685101 176717869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13294)) 176717869 176750637 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 176717869 176750637).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13294 176717869 176750637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13295)) 176750637 176783405 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 176750637 176783405).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13295 176750637 176783405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13297)) 176783405 176816173 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 176783405 176816173).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13297 176783405 176816173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 176685101 176750637).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 176685101 ≤ 176717869)
    (by decide : 176717869 ≤ 176750637) block0 block1

theorem join_0_1 : (twinPrimeSegment 176750637 176816173).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 176750637 ≤ 176783405)
    (by decide : 176783405 ≤ 176816173) block2 block3

theorem join_1_0 : (twinPrimeSegment 176685101 176816173).card = 515 := by
  simpa using combineTwinPrimeSegments (by decide : 176685101 ≤ 176750637)
    (by decide : 176750637 ≤ 176816173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 176685101 176816173).card = 515 := join_1_0

end S084C04
end Sude.GeneratedTwinScan
