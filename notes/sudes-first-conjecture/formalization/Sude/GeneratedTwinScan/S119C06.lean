import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15823)) 250347565 250380333 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 250347565 250380333).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15823 250347565 250380333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15824)) 250380333 250413101 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 250380333 250413101).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15824 250380333 250413101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15825)) 250413101 250445869 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 250413101 250445869).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15825 250413101 250445869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15826)) 250445869 250478637 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 250445869 250478637).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15826 250445869 250478637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 250347565 250413101).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 250347565 ≤ 250380333)
    (by decide : 250380333 ≤ 250413101) block0 block1

theorem join_0_1 : (twinPrimeSegment 250413101 250478637).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 250413101 ≤ 250445869)
    (by decide : 250445869 ≤ 250478637) block2 block3

theorem join_1_0 : (twinPrimeSegment 250347565 250478637).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 250347565 ≤ 250413101)
    (by decide : 250413101 ≤ 250478637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 250347565 250478637).card = 488 := join_1_0

end S119C06
end Sude.GeneratedTwinScan
