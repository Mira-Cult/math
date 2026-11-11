import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21176)) 448397357 448430125 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 448397357 448430125).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21176 448397357 448430125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21176)) 448430125 448462893 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 448430125 448462893).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21176 448430125 448462893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21177)) 448462893 448495661 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 448462893 448495661).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21177 448462893 448495661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21178)) 448495661 448528429 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 448495661 448528429).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21178 448495661 448528429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 448397357 448462893).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 448397357 ≤ 448430125)
    (by decide : 448430125 ≤ 448462893) block0 block1

theorem join_0_1 : (twinPrimeSegment 448462893 448528429).card = 190 := by
  simpa using combineTwinPrimeSegments (by decide : 448462893 ≤ 448495661)
    (by decide : 448495661 ≤ 448528429) block2 block3

theorem join_1_0 : (twinPrimeSegment 448397357 448528429).card = 407 := by
  simpa using combineTwinPrimeSegments (by decide : 448397357 ≤ 448462893)
    (by decide : 448462893 ≤ 448528429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 448397357 448528429).card = 407 := join_1_0

end S213C13
end Sude.GeneratedTwinScan
