import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18616)) 346554413 346587181 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 346554413 346587181).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18616 346554413 346587181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18617)) 346587181 346619949 = 91 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 346587181 346619949).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18617 346587181 346619949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18618)) 346619949 346652717 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 346619949 346652717).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18618 346619949 346652717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18619)) 346652717 346685485 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 346652717 346685485).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18619 346652717 346685485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 346554413 346619949).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 346554413 ≤ 346587181)
    (by decide : 346587181 ≤ 346619949) block0 block1

theorem join_0_1 : (twinPrimeSegment 346619949 346685485).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 346619949 ≤ 346652717)
    (by decide : 346652717 ≤ 346685485) block2 block3

theorem join_1_0 : (twinPrimeSegment 346554413 346685485).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 346554413 ≤ 346619949)
    (by decide : 346619949 ≤ 346685485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 346554413 346685485).card = 426 := join_1_0

end S165C04
end Sude.GeneratedTwinScan
