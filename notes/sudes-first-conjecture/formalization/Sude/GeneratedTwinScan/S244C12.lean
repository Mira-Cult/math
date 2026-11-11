import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22656)) 513277997 513310765 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 513277997 513310765).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22656 513277997 513310765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22657)) 513310765 513343533 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 513310765 513343533).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22657 513310765 513343533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22657)) 513343533 513376301 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 513343533 513376301).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22657 513343533 513376301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22658)) 513376301 513409069 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 513376301 513409069).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22658 513376301 513409069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 513277997 513343533).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 513277997 ≤ 513310765)
    (by decide : 513310765 ≤ 513343533) block0 block1

theorem join_0_1 : (twinPrimeSegment 513343533 513409069).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 513343533 ≤ 513376301)
    (by decide : 513376301 ≤ 513409069) block2 block3

theorem join_1_0 : (twinPrimeSegment 513277997 513409069).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 513277997 ≤ 513343533)
    (by decide : 513343533 ≤ 513409069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 513277997 513409069).card = 447 := join_1_0

end S244C12
end Sude.GeneratedTwinScan
