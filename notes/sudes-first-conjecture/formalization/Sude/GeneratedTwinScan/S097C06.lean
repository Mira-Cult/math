import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14291)) 204210221 204242989 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 204210221 204242989).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14291 204210221 204242989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14292)) 204242989 204275757 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 204242989 204275757).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14292 204242989 204275757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14293)) 204275757 204308525 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 204275757 204308525).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14293 204275757 204308525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14294)) 204308525 204341293 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 204308525 204341293).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14294 204308525 204341293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 204210221 204275757).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 204210221 ≤ 204242989)
    (by decide : 204242989 ≤ 204275757) block0 block1

theorem join_0_1 : (twinPrimeSegment 204275757 204341293).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 204275757 ≤ 204308525)
    (by decide : 204308525 ≤ 204341293) block2 block3

theorem join_1_0 : (twinPrimeSegment 204210221 204341293).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 204210221 ≤ 204275757)
    (by decide : 204275757 ≤ 204341293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 204210221 204341293).card = 479 := join_1_0

end S097C06
end Sude.GeneratedTwinScan
