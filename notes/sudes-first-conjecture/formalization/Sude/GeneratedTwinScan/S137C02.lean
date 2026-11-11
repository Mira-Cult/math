import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16958)) 287572013 287604781 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 287572013 287604781).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16958 287572013 287604781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16959)) 287604781 287637549 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 287604781 287637549).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16959 287604781 287637549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16960)) 287637549 287670317 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 287637549 287670317).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16960 287637549 287670317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16961)) 287670317 287703085 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 287670317 287703085).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16961 287670317 287703085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 287572013 287637549).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 287572013 ≤ 287604781)
    (by decide : 287604781 ≤ 287637549) block0 block1

theorem join_0_1 : (twinPrimeSegment 287637549 287703085).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 287637549 ≤ 287670317)
    (by decide : 287670317 ≤ 287703085) block2 block3

theorem join_1_0 : (twinPrimeSegment 287572013 287703085).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 287572013 ≤ 287637549)
    (by decide : 287637549 ≤ 287703085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 287572013 287703085).card = 463 := join_1_0

end S137C02
end Sude.GeneratedTwinScan
