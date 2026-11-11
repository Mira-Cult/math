import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13595)) 184811565 184844333 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 184811565 184844333).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13595 184811565 184844333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13596)) 184844333 184877101 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 184844333 184877101).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13596 184844333 184877101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13598)) 184877101 184909869 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 184877101 184909869).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13598 184877101 184909869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13599)) 184909869 184942637 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 184909869 184942637).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13599 184909869 184942637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 184811565 184877101).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 184811565 ≤ 184844333)
    (by decide : 184844333 ≤ 184877101) block0 block1

theorem join_0_1 : (twinPrimeSegment 184877101 184942637).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 184877101 ≤ 184909869)
    (by decide : 184909869 ≤ 184942637) block2 block3

theorem join_1_0 : (twinPrimeSegment 184811565 184942637).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 184811565 ≤ 184877101)
    (by decide : 184877101 ≤ 184942637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 184811565 184942637).card = 485 := join_1_0

end S088C02
end Sude.GeneratedTwinScan
