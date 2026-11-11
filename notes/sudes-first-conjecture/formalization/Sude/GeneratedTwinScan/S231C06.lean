import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22028)) 485228589 485261357 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 485228589 485261357).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22028 485228589 485261357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22029)) 485261357 485294125 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 485261357 485294125).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22029 485261357 485294125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22030)) 485294125 485326893 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 485294125 485326893).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22030 485294125 485326893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22030)) 485326893 485359661 = 88 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 485326893 485359661).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22030 485326893 485359661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 485228589 485294125).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 485228589 ≤ 485261357)
    (by decide : 485261357 ≤ 485294125) block0 block1

theorem join_0_1 : (twinPrimeSegment 485294125 485359661).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 485294125 ≤ 485326893)
    (by decide : 485326893 ≤ 485359661) block2 block3

theorem join_1_0 : (twinPrimeSegment 485228589 485359661).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 485228589 ≤ 485294125)
    (by decide : 485294125 ≤ 485359661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 485228589 485359661).card = 418 := join_1_0

end S231C06
end Sude.GeneratedTwinScan
