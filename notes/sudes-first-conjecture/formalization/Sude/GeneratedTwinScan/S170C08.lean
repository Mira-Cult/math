import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18910)) 357564461 357597229 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 357564461 357597229).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18910 357564461 357597229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18911)) 357597229 357629997 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 357597229 357629997).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18911 357597229 357629997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18911)) 357629997 357662765 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 357629997 357662765).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18911 357629997 357662765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18912)) 357662765 357695533 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 357662765 357695533).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18912 357662765 357695533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 357564461 357629997).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 357564461 ≤ 357597229)
    (by decide : 357597229 ≤ 357629997) block0 block1

theorem join_0_1 : (twinPrimeSegment 357629997 357695533).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 357629997 ≤ 357662765)
    (by decide : 357662765 ≤ 357695533) block2 block3

theorem join_1_0 : (twinPrimeSegment 357564461 357695533).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 357564461 ≤ 357629997)
    (by decide : 357629997 ≤ 357695533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 357564461 357695533).card = 445 := join_1_0

end S170C08
end Sude.GeneratedTwinScan
