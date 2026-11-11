import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20551)) 422314029 422346797 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 422314029 422346797).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20551 422314029 422346797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20551)) 422346797 422379565 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 422346797 422379565).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20551 422346797 422379565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20552)) 422379565 422412333 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 422379565 422412333).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20552 422379565 422412333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20553)) 422412333 422445101 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 422412333 422445101).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20553 422412333 422445101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 422314029 422379565).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 422314029 ≤ 422346797)
    (by decide : 422346797 ≤ 422379565) block0 block1

theorem join_0_1 : (twinPrimeSegment 422379565 422445101).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 422379565 ≤ 422412333)
    (by decide : 422412333 ≤ 422445101) block2 block3

theorem join_1_0 : (twinPrimeSegment 422314029 422445101).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 422314029 ≤ 422379565)
    (by decide : 422379565 ≤ 422445101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 422314029 422445101).card = 455 := join_1_0

end S201C06
end Sude.GeneratedTwinScan
