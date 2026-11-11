import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13024)) 169607213 169639981 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 169607213 169639981).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13024 169607213 169639981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13025)) 169639981 169672749 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 169639981 169672749).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13025 169639981 169672749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13027)) 169672749 169705517 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 169672749 169705517).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13027 169672749 169705517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13028)) 169705517 169738285 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 169705517 169738285).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13028 169705517 169738285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 169607213 169672749).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 169607213 ≤ 169639981)
    (by decide : 169639981 ≤ 169672749) block0 block1

theorem join_0_1 : (twinPrimeSegment 169672749 169738285).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 169672749 ≤ 169705517)
    (by decide : 169705517 ≤ 169738285) block2 block3

theorem join_1_0 : (twinPrimeSegment 169607213 169738285).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 169607213 ≤ 169672749)
    (by decide : 169672749 ≤ 169738285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 169607213 169738285).card = 457 := join_1_0

end S080C14
end Sude.GeneratedTwinScan
