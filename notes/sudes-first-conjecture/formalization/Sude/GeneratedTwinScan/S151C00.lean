import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17796)) 316669997 316702765 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 316669997 316702765).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17796 316669997 316702765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17797)) 316702765 316735533 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 316702765 316735533).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17797 316702765 316735533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17797)) 316735533 316768301 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 316735533 316768301).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17797 316735533 316768301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17798)) 316768301 316801069 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 316768301 316801069).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17798 316768301 316801069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 316669997 316735533).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 316669997 ≤ 316702765)
    (by decide : 316702765 ≤ 316735533) block0 block1

theorem join_0_1 : (twinPrimeSegment 316735533 316801069).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 316735533 ≤ 316768301)
    (by decide : 316768301 ≤ 316801069) block2 block3

theorem join_1_0 : (twinPrimeSegment 316669997 316801069).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 316669997 ≤ 316735533)
    (by decide : 316735533 ≤ 316801069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 316669997 316801069).card = 452 := join_1_0

end S151C00
end Sude.GeneratedTwinScan
