import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20567)) 422969389 423002157 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 422969389 423002157).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20567 422969389 423002157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20567)) 423002157 423034925 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 423002157 423034925).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20567 423002157 423034925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20568)) 423034925 423067693 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 423034925 423067693).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20568 423034925 423067693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20569)) 423067693 423100461 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 423067693 423100461).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20569 423067693 423100461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 422969389 423034925).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 422969389 ≤ 423002157)
    (by decide : 423002157 ≤ 423034925) block0 block1

theorem join_0_1 : (twinPrimeSegment 423034925 423100461).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 423034925 ≤ 423067693)
    (by decide : 423067693 ≤ 423100461) block2 block3

theorem join_1_0 : (twinPrimeSegment 422969389 423100461).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 422969389 ≤ 423034925)
    (by decide : 423034925 ≤ 423100461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 422969389 423100461).card = 441 := join_1_0

end S201C11
end Sude.GeneratedTwinScan
